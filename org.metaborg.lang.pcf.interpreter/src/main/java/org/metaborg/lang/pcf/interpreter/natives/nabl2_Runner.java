
package org.metaborg.lang.pcf.interpreter.natives;

import org.metaborg.lang.pcf.interpreter.generated.PCFEntryPoint;
import org.apache.commons.vfs2.FileObject;
import org.metaborg.core.MetaborgException;
import org.metaborg.meta.lang.dynsem.interpreter.DynSemRunner;
import org.metaborg.meta.lang.dynsem.interpreter.DynSemRunnerModule;
import org.metaborg.spoofax.core.Spoofax;

import com.google.inject.Module;

public class nabl2_Runner extends DynSemRunner {

  public nabl2_Runner(Spoofax S) throws MetaborgException {
    super(S, "PCF", new PCFEntryPoint());
  }
 
  public static void main(String... args) {
        if(args.length < 1) {
            System.err.println("Usage: "+nabl2_Runner.class.getName()+" FILES");
            return;
        }
        try(Spoofax S = new Spoofax(new DynSemRunnerModule(), new Module[0])) {
          DynSemRunner runner = new nabl2_Runner(S);
          for(String fileName : args) {
            FileObject file = S.resourceService.resolve(fileName);
            Object result = runner.run(file, System.in, System.out, System.err);
            System.out.println(result);
          }
        } catch (MetaborgException e) {
            e.printStackTrace(System.err);
        }
    }
}
