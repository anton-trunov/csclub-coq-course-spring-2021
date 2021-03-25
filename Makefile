SOURCES := $(shell find lectures -name '*.v')
HTMLS := $(SOURCES:%.v=%.html)

.PHONY: doc
doc: $(HTMLS)

lectures/%.html: lectures/%.v
	alectryon.py --frontend coq+rst --backend webpage $< -o $@
