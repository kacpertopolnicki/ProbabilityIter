import argparse

import examples

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument("--examples" , "-e" , action = "store_true" , help = "Run examples.")
    args = parser.parse_args()

    if args.examples:
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
