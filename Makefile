SOURCES := $(shell find lectures -name '*.v')
HTMLS := $(SOURCES:%.v=%.html)

.PHONY: doc
doc: $(HTMLS)

# See https://github.com/cpitclaudel/alectryon/issues/43
# to understand why --expect-unexpected flag is needed here
lectures/%.html: lectures/%.v
	alectryon.py --expect-unexpected --frontend coq+rst --backend webpage $< -o $@
