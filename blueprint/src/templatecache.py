"""Reuse compiled Jinja templates within a plasTeX web build.

plasTeX 3.1's PageTemplate renderer creates one Jinja environment per template,
then recompiles its source for every rendered node. Cache compilation in those
environments only; leave rendering and error handling to plasTeX. Nothing is
cached on disk or shared between builds. Remove this workaround when upstream
compiles each template once. Loaded only by web.tex; remove its templatecache
package line to disable the workaround.
"""


def cache_templates(renderer):
    class CachedEnvironment(renderer.Environment):
        def __init__(self, *args, **kwargs):
            super().__init__(*args, **kwargs)
            self._blueprint_templates = {}

        def from_string(self, source, globals=None, template_class=None):
            # The renderer uses plain source strings without these overrides.
            if not isinstance(source, str) or globals is not None or template_class is not None:
                return super().from_string(source, globals=globals, template_class=template_class)
            if source not in self._blueprint_templates:
                self._blueprint_templates[source] = super().from_string(source)
            return self._blueprint_templates[source]

    renderer.Environment = CachedEnvironment


def ProcessOptions(options, document):
    import plasTeX.Renderers.PageTemplate as renderer

    cache_templates(renderer)
