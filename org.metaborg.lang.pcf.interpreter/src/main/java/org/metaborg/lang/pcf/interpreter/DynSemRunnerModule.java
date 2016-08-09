package org.metaborg.lang.pcf.interpreter;

import org.metaborg.core.project.ConfigBasedProjectService;
import org.metaborg.core.project.IProjectService;
import org.metaborg.spoofax.core.SpoofaxModule;

import com.google.inject.Singleton;

class DynSemRunnerModule extends SpoofaxModule {
	
	@Override
	protected void bindProject() {
        bind(IProjectService.class).to(ConfigBasedProjectService.class).in(Singleton.class);
	}
}