"""Add the sector graph pages built by `just web` to HTML5 navigation."""

from plasTeX.PackageResource import PackageResource


class SectorGraphLinks(PackageResource):
    key = "extra_toc_items"


def ProcessOptions(options, document):
    document.addPackageResource(SectorGraphLinks(data=[
        {"text": "Even–even dependency graph",
         "url": "dep_graph_thm-ee-exclusion.html"},
        {"text": "Odd–odd dependency graph",
         "url": "dep_graph_thm-dd-exclusion.html"},
        {"text": "Mixed dependency graph",
         "url": "dep_graph_thm-mixed-exclusion.html"},
    ]))
