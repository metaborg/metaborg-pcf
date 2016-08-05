package org.metaborg.lang.pcf.interpreter;

import java.io.IOException;

import org.apache.commons.vfs2.FileObject;
import org.metaborg.core.MetaborgException;
import org.metaborg.core.analysis.IAnalyzeResult;
import org.metaborg.core.context.IContext;
import org.metaborg.core.language.ILanguage;
import org.metaborg.core.language.ILanguageDiscoveryRequest;
import org.metaborg.core.language.ILanguageImpl;
import org.metaborg.core.project.IProject;
import org.metaborg.core.project.ISimpleProjectService;
import org.metaborg.lang.pcf.interpreter.generated.PCFEntryPoint;
import org.metaborg.meta.lang.dynsem.interpreter.nodes.rules.RuleResult;
import org.metaborg.spoofax.core.Spoofax;
import org.metaborg.spoofax.core.unit.ISpoofaxAnalyzeUnit;
import org.metaborg.spoofax.core.unit.ISpoofaxAnalyzeUnitUpdate;
import org.metaborg.spoofax.core.unit.ISpoofaxInputUnit;
import org.metaborg.spoofax.core.unit.ISpoofaxParseUnit;
import org.spoofax.interpreter.terms.IStrategoTerm;

import com.google.inject.Module;

public class PCFRunner {

    public static void main(String... args) throws MetaborgException {
        if(args.length != 1) {
            throw new MetaborgException("Usage: "+PCFRunner.class.getName()+" <file>");
        }
        String fileName = args[0];
        IStrategoTerm program;
        try(Spoofax S = new Spoofax(new PCFRunnerModule(), new Module[0])) {
            FileObject file = S.resourceService.resolve(fileName);
            
            FileObject projectDir = file.getParent();
            ISimpleProjectService projectService = S.injector.getInstance(ISimpleProjectService.class);
            IProject project = projectService.create(projectDir);
            
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

            ILanguage lang = S.languageService.getLanguage("PCF");
            if(lang == null) {
                throw new MetaborgException("Cannot find language PCF.");
            }
            ILanguageImpl langImpl = lang.activeImpl();
            if(langImpl == null) {
                throw new MetaborgException("Language PCF has no active implementation.");
            }

            String text = S.sourceTextService.text(file);
            ISpoofaxInputUnit input = S.unitService.inputUnit(file, text, langImpl, null);

            ISpoofaxParseUnit parsed = S.syntaxService.parse(input);

            IContext context = S.contextService.get(file, project, langImpl);
            IAnalyzeResult<ISpoofaxAnalyzeUnit, ISpoofaxAnalyzeUnitUpdate> analyzed =
                    S.analysisService.analyze(parsed, context);

            program = analyzed.result().ast();
        } catch (IOException e) {
            throw new MetaborgException("Analysis failed.", e);
        }
        try {
            RuleResult result = PCFEntryPoint.evaluate(program, System.in, System.out, System.err);
            System.out.println(result.result);
        } catch (Exception e) {
            throw new MetaborgException("Evaluation failed.", e);
        }
        
    }

}
