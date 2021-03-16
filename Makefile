SOURCES := $(shell find lectures -name '*.v')
HTMLS := $(SOURCES:%.v=%.html)

doc: $(HTMLS)

lectures/%.html: lectures/%.v
	alectryon.py --frontend coq+rst --backend webpage $< -o $@
