all:
	$(MAKE) -C proof ide
	$(MAKE) -C proof

clean:
	$(MAKE) -C proof clean

cleanall: clean
	$(MAKE) -C lib/tlc clean
	$(RM) doc/*.html
	$(RM) doc/*.css
