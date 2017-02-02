package org.metaborg.lang.pcf.interpreter.natives;

import org.metaborg.meta.lang.dynsem.interpreter.nodes.building.TermBuild;

import com.oracle.truffle.api.dsl.NodeChild;
import com.oracle.truffle.api.dsl.Specialization;
import com.oracle.truffle.api.source.SourceSection;

@NodeChild(value = "print", type = TermBuild.class)
public abstract class printStringI_1 extends TermBuild {

      public printStringI_1(SourceSection source) {
              super(source);
      }

      @Specialization
      public Object doInt(Object s) {
        System.out.println(s);
        return s;
      }

      public static TermBuild create(SourceSection source, TermBuild print) {
              return printStringI_1NodeGen.create(source, print);
      }

}