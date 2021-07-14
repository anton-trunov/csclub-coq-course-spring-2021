SOURCES := $(shell find lectures -name '*.v')
HTMLS := $(SOURCES:%.v=%.html)

.PHONY: doc
doc: $(HTMLS)

# See https://github.com/cpitclaudel/alectryon/issues/43
# to understand why --expect-unexpected flag is needed here
lectures/%.html: lectures/%.v
	alectryon --expect-unexpected --frontend coq+rst --backend webpage $< -o $@
<<<<<<< HEAD

.PHONY: clean
clean:
	rm -f lectures/lecture*.html
=======
>>>>>>> f1e4242 (reorganize files)
