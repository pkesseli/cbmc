default: tests.log

test:
	@../test.pl -c ../chain.sh

tests.log: ../test.pl
	@../test.pl -c ../chain.sh

show:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			vim -o "$$dir/*.c" "$$dir/*.out"; \
		fi; \
	done;
