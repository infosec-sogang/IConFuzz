BUILDDIR=$(shell pwd)/build

all: $(BUILDDIR) IConFuzz

clean:
	@dotnet clean -c Release
	@rm -rf $(BUILDDIR)

$(BUILDDIR):
	@mkdir -p $(BUILDDIR)

IConFuzz:
	@dotnet build -c Release --property:OutputPath=$(BUILDDIR)

.PHONY: all clean IConFuzz
