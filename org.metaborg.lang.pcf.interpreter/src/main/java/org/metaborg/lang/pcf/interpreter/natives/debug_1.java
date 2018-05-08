package org.metaborg.lang.pcf.interpreter.natives;

import org.metaborg.meta.lang.dynsem.interpreter.nodes.building.TermBuild;
import org.metaborg.meta.lang.dynsem.interpreter.terms.ITerm;

import com.oracle.truffle.api.dsl.NodeChild;
import com.oracle.truffle.api.dsl.Specialization;
import com.oracle.truffle.api.source.SourceSection;

@NodeChild(value = "term", type = TermBuild.class)
public abstract class debug_1 extends TermBuild {

    public debug_1(SourceSection source) {
        super(source);
    }

    @Specialization
    public String doTerm(ITerm term) {
        return term.toString();
    }

    public static TermBuild create(SourceSection source, TermBuild term) {
        return debug_1NodeGen.create(source, term);
    }

}