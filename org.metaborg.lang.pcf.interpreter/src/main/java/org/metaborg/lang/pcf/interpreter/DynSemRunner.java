package org.metaborg.lang.pcf.interpreter;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;

import org.apache.commons.vfs2.FileObject;
import org.metaborg.core.MetaborgConstants;
import org.metaborg.core.MetaborgException;
import org.metaborg.core.analysis.IAnalyzeResult;
import org.metaborg.core.context.IContext;
import org.metaborg.core.language.ILanguage;
import org.metaborg.core.language.ILanguageDiscoveryRequest;
import org.metaborg.core.language.ILanguageImpl;
import org.metaborg.core.project.IProject;
import org.metaborg.core.project.IProjectService;
import org.metaborg.lang.pcf.interpreter.generated.PCFEntryPoint;
import org.metaborg.meta.lang.dynsem.interpreter.DynSemEntryPoint;
import org.metaborg.meta.lang.dynsem.interpreter.nodes.rules.RuleResult;
import org.metaborg.spoofax.core.Spoofax;
import org.metaborg.spoofax.core.unit.ISpoofaxAnalyzeUnit;
import org.metaborg.spoofax.core.unit.ISpoofaxAnalyzeUnitUpdate;
import org.metaborg.spoofax.core.unit.ISpoofaxInputUnit;
import org.metaborg.spoofax.core.unit.ISpoofaxParseUnit;
import org.metaborg.util.concurrent.IClosableLock;
import org.spoofax.interpreter.terms.IStrategoTerm;

import com.google.inject.Module;

public class DynSemRunner {

	private final Spoofax S;
	private final ILanguageImpl language;
	private final DynSemEntryPoint interpreter;
	
	private DynSemRunner(Spoofax S, String languageName, DynSemEntryPoint interpreter)
			throws MetaborgException {
		this.S = S;
		this.language = loadLanguage(languageName);
		this.interpreter = interpreter;
	}
	
	private ILanguageImpl loadLanguage(String languageName)
			throws MetaborgException {
		String spoofaxPath = System.getenv("SPOOFAXPATH");
		if(spoofaxPath != null) {
			for(String spoofaxDirName : spoofaxPath.split(":")) {
				if(spoofaxDirName.isEmpty()) {
					continue;
				}
				FileObject spoofaxDir = S.resourceService.resolve(spoofaxDirName);
				for(ILanguageDiscoveryRequest req : S.languageDiscoveryService.request(spoofaxDir)) {
					S.languageDiscoveryService.discover(req);
				}
			}
		}
		ILanguage lang = S.languageService.getLanguage(languageName);
		if(lang == null) {
			throw new MetaborgException("Cannot find language PCF.");
		}
		ILanguageImpl langImpl = lang.activeImpl();
		if(langImpl == null) {
			throw new MetaborgException("Language PCF has no active implementation.");
		}
		return langImpl;
	}
	

    public Object run(FileObject file, InputStream in, OutputStream out, OutputStream err)
    		throws MetaborgException {
        IStrategoTerm program;
        try {
			IProjectService projectService = S.injector.getInstance(IProjectService.class);
			IProject project = projectService.get(file);
			if(project == null) {
				throw new MetaborgException("File is not part of a project. Missing "+MetaborgConstants.FILE_CONFIG+"?");
			}
        	
            String text = S.sourceTextService.text(file);
            ISpoofaxInputUnit input = S.unitService.inputUnit(file, text, language, null);
            ISpoofaxParseUnit parsed = S.syntaxService.parse(input);

            IContext context = S.contextService.get(file, project, language);
			IAnalyzeResult<ISpoofaxAnalyzeUnit, ISpoofaxAnalyzeUnitUpdate> analyzed;
            try(IClosableLock lock = context.write()) {
            	analyzed = S.analysisService.analyze(parsed, context);
            }
            program = analyzed.result().ast();
        } catch (IOException e) {
            throw new MetaborgException("Analysis failed.", e);
        }
        try {
            RuleResult result = interpreter.getCallable(program, in, out, err).call();
            return result.result;
        } catch (Exception e) {
            throw new MetaborgException("Evaluation failed.", e);
        }
    }

	public static void main(String... args) throws MetaborgException {
        if(args.length < 1) {
            throw new MetaborgException("Usage: "+DynSemRunner.class.getName()+" FILES");
        }
        try(Spoofax S = new Spoofax(new DynSemRunnerModule(), new Module[0])) {
        	DynSemRunner runner = new DynSemRunner(S, "PCF", new PCFEntryPoint());
        	for(String fileName : args) {
				FileObject file = S.resourceService.resolve(fileName);
				Object result = runner.run(file, System.in, System.out, System.err);
				System.out.println(result);
        	}
        } catch (MetaborgException e) {
            throw new MetaborgException("Evaluation failed.", e);
        }
    }

}