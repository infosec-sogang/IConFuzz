BUILDDIR=$(shell pwd)/build

all: solAnalysis

solAnalysis:
		@mkdir -p $(BUILDDIR)
		@dotnet build -c Release -o $(BUILDDIR) solAnalysis.fsproj

clean:
		@dotnet clean -c Debug
		@dotnet clean -c Release
		@rm -rf $(BUILDDIR)

.PHONY: EVMAnalysis all clean

