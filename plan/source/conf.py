# See https://www.sphinx-doc.org/en/master/usage/configuration.html

project = 'Fault Checker'
copyright = '2025, Riverside Research'
author = 'David Swasey'

# Consistent with sphinx conventions but probably irrelevant.
# See ./docutils.conf:/tab_width
tab_width = 3

extensions = [
	'sphinxcontrib.bibtex'
]
source_suffix = {
	'.rst': 'restructuredtext',
}
bibtex_bibfiles = ['bib.bib']

templates_path = ['_templates']
exclude_patterns = []

html_theme = 'alabaster'
html_static_path = ['_static']

# See https://docs.mathjax.org/en/latest/input/tex/macros.html
# DO NOT USE (buggy): `'inlineMath': [['$', '$'], ['\\(', '\\)']],`.
mathjax3_config = {
	'tex': {
		'macros': {
			'smove': '\\operatorname{smove}',
			'vote': '\\operatorname{vote}',
			'dom': '\\operatorname{dom}',
			'sp': '\\operatorname{sp}',
			'loc': '\\mathit{loc}',
			'state': 's',
				'mem': '\mathit{mem}',
				'rs': '\mathit{rs}',
				'color': '\mathit{cs}',
					'red': '\\text{red}',
					'green': '\\text{green}',
					'blue': '\\text{blue}',
			'RA': '\\text{RA}',
			'SP': '\\text{SP}',
			'PC': '\\text{PC}',
		}
	}
}
