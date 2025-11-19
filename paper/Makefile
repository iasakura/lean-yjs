TEX=paper
MARGIN?=40

.PHONY: all watch clean arxiv distdir rules clean-rules rules-transparent svg

all:
	latexmk -pdf -interaction=nonstopmode -halt-on-error $(TEX).tex

watch:
	latexmk -pdf -pvc -interaction=nonstopmode $(TEX).tex

clean:
	latexmk -C $(TEX).tex
	rm -rf dist
	latexmk -C rules.tex 2>/dev/null || true

distdir:
	mkdir -p dist

# Build .bbl and create a minimal arXiv-ready zip
arxiv: all distdir
	# Ensure .bbl is up to date
	bibtex $(TEX) || true
	latexmk -pdf -interaction=nonstopmode -halt-on-error $(TEX).tex
	zip -j dist/$(TEX)-arxiv.zip $(TEX).tex $(TEX).bbl refs.bib || true
	# Include figures directory if present
	if [ -d figures ]; then cd figures && zip -r ../dist/$(TEX)-arxiv.zip .; fi

# --- Rules diagram (PNG) ---
rules.pdf: yjslt.tex rules.tex
	latexmk -pdf -interaction=nonstopmode -halt-on-error rules.tex

rules.png: rules.pdf
	@if command -v magick >/dev/null 2>&1; then \
		magick -density 400 \
			-define pdf:use-cropbox=true \
			-colorspace sRGB -type TrueColor -depth 8 \
			-background white -alpha remove -alpha off -flatten \
			-trim +repage -bordercolor white -border $(MARGIN) \
			-filter Lanczos -quality 95 rules.pdf rules.png; \
	else \
		convert -density 400 \
			-define pdf:use-cropbox=true \
			-colorspace sRGB -type TrueColor -depth 8 \
			-background white -alpha remove -alpha off -flatten \
			-trim +repage -bordercolor white -border $(MARGIN) \
			-filter Lanczos -quality 95 rules.pdf rules.png; \
	fi

# Transparent PNG via Ghostscript (respects cropbox)
rules.transparent.png: rules.pdf
	gs -dSAFER -dBATCH -dNOPAUSE -sDEVICE=pngalpha -r400 -dUseCropBox \
		-dTextAlphaBits=4 -dGraphicsAlphaBits=4 \
		-sOutputFile=$@ $<
	@if command -v magick >/dev/null 2>&1; then \
		magick $@ -trim +repage -bordercolor none -border $(MARGIN) $@; \
	else \
		mogrify -trim +repage -bordercolor none -border $(MARGIN) $@ || convert $@ -trim +repage -bordercolor none -border $(MARGIN) $@; \
	fi

# SVG vector export (transparent by nature)
rules.svg: rules.pdf
	pdf2svg rules.pdf rules.svg

rules-transparent: rules.transparent.png
svg: rules.svg

rules: rules.png

clean-rules:
	rm -f rules.aux rules.log rules.pdf rules.out rules.fls rules.fdb_latexmk rules.synctex.gz rules.png
