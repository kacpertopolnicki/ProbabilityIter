import argparse

def run_examples():
    import examples
    print()
    print("--------------")
    print("examples/example_no_constraints.py")
    print("--------------")

    examples.example_no_constraints.main()

    print()
    print("--------------")
    print("examples/example_constraints.py")
    print("--------------")

    examples.example_constraints.main()

    print()
    print("--------------")
    print("examples/example_optimize.py")
    print("--------------")

    examples.example_optimize.main()

def run_linter(input_file):
    if args.input is None:
        raise ValueError("Expecting input file.")
    import re
    file = None
    with open(input_file , "r") as f:
        file = f.read()

    from html.parser import HTMLParser 
    from sympy import symbols
    from sympy import true

    class MyHTMLParser(HTMLParser):
        def __init__(self):
            HTMLParser.__init__(self)
            self.tag = None
            self.data = None
            self.all = dict()

        def print_all(self):
            for s in self.all:
                print(s)
                print(self.all[s])
                print()

        def handle_starttag(self, tag, attrs):
            self.tag = (tag , tuple(attrs)) 

        def handle_endtag(self, tag):
            if self.tag is not None:
                self.all[self.tag] = self.data
            self.tag = None
            self.data = None

        def handle_data(self, data):
            self.data = data

    parser = MyHTMLParser()
    parser.feed(file)
    parser.print_all()

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument("--examples" , "-e" , action = "store_true" , help = "Run examples.")
    parser.add_argument("--input" , "-i" , help = "Path to input file for linter.")
    args = parser.parse_args()

    if args.examples:
        run_examples()
    elif args.input is not None:
        run_linter(args.input)

