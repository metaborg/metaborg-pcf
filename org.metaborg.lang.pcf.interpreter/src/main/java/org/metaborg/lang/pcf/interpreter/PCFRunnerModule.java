package org.metaborg.lang.pcf.interpreter;

import org.metaborg.core.project.IProjectService;
import org.metaborg.core.project.ISimpleProjectService;
import org.metaborg.core.project.SimpleProjectService;
import org.metaborg.spoofax.core.SpoofaxModule;

import com.google.inject.Singleton;

class PCFRunnerModule extends SpoofaxModule {
	
	@Override
	protected void bindProject() {
        bind(ISimpleProjectService.class).to(SimpleProjectService.class).in(Singleton.class);
        bind(IProjectService.class).to(ISimpleProjectService.class).in(Singleton.class);
	}
	
}