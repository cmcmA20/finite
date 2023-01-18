AGDA ?= agda
.PHONY: listings clean Everything.agda

default: everything

everything: Everything.agda
	$(AGDA) -i. -isrc Everything.agda

test:
	$(AGDA) -i. -isrc -iexamples examples/SAT.agda

clean:
	find . -type f -name '*.agdai' -delete

Everything.agda:
	git ls-tree --full-tree -r --name-only HEAD | grep '^src/[^\.]*.agda' | sed -e 's|^src/[/]*|import |' -e 's|/|.|g' -e 's/.agda//' -e '/import Everything/d' | LC_COLLATE='C' sort > Everything.agda
