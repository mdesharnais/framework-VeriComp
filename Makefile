ISABELLE = isabelle
FLAGS = -c -v

build:
	$(ISABELLE) build $(FLAGS) -D .

debug:
	$(ISABELLE) build $(FLAGS) -o quick_and_dirty -D .

