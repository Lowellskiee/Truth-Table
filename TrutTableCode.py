import itertools
import re

class LogicOperator:
    def __init__(self, name, func):
        self.name = name
        self.func = func

class LogicExpressionParser:
    def __init__(self):
        self.operators = {
            'NOT': LogicOperator('NOT', lambda a: not a),
            'AND': LogicOperator('AND', lambda a, b: a and b),
            'OR': LogicOperator('OR', lambda a, b: a or b),
            'IMPLIES': LogicOperator('IMPLIES', lambda a, b: (not a) or b),
            'IFF': LogicOperator('IFF', lambda a, b: a == b)
        }
        self.symbol_map = {
            '~': 'NOT',
            '^': 'AND',
            'or': 'OR',
            '->': 'IMPLIES',
            '<->': 'IFF'
        }
        self.variables_set = {'P', 'Q', 'R'}
        self.precedence_levels = {
            'NOT': 3,
            'AND': 2,
            'OR': 2,
            'IMPLIES': 1,
            'IFF': 1
        }
        self.associativity_map = {
            'NOT': 'RIGHT',
            'AND': 'LEFT',
            'OR': 'LEFT',
            'IMPLIES': 'LEFT',
            'IFF': 'LEFT'
        }

    def tokenize_expression(self, expression):
        token_spec = [
            ('LPAREN', r'\('),
            ('RPAREN', r'\)'),
            ('OPERATOR', r'<->|->|~|\^|or|AND|OR|NOT|IMPLIES|IFF'),
            ('VARIABLE', r'[PQRpqr]'),
            ('CONSTANT', r'TRUE|FALSE'),
            ('WHITESPACE', r'\s+'),
            ('UNKNOWN', r'.')
        ]
        regex = '|'.join(f'(?P<{name}>{pattern})' for name, pattern in token_spec)
        tokens = []
        for match in re.finditer(regex, expression):
            kind = match.lastgroup
            value = match.group()
            if kind == 'OPERATOR':
                tokens.append(self.symbol_map.get(value.upper(), value.upper()))
            elif kind == 'VARIABLE':
                tokens.append(value.upper())
            elif kind in ('CONSTANT', 'LPAREN', 'RPAREN'):
                tokens.append(value.upper())
            elif kind == 'WHITESPACE':
                continue
            else:
                raise ValueError(f"Unexpected character: {value}")
        return tokens

    def convert_to_postfix(self, tokens):
        output = []
        operators = []
        
        for token in tokens:
            if token in self.variables_set or token in {'TRUE', 'FALSE'}:
                output.append(token)
            elif token in self.operators:
                while (operators and operators[-1] in self.operators and
                       ((self.associativity_map[token] == 'LEFT' and self.precedence_levels[token] <= self.precedence_levels[operators[-1]]) or
                        (self.associativity_map[token] == 'RIGHT' and self.precedence_levels[token] < self.precedence_levels[operators[-1]]))):
                    output.append(operators.pop())
                operators.append(token)
            elif token == '(':
                operators.append(token)
            elif token == ')':
                while operators and operators[-1] != '(':
                    output.append(operators.pop())
                operators.pop()  # Pop the '('
            else:
                raise ValueError(f"Unknown token: {token}")

        while operators:
            if operators[-1] in ('(', ')'):
                raise ValueError("Mismatched parentheses")
            output.append(operators.pop())
        
        return output

    def evaluate_postfix_expression(self, postfix_tokens, values):
        stack = []
        results = []
        for token in postfix_tokens:
            if token in self.variables_set:
                stack.append((token, values[token]))
            elif token in {'TRUE', 'FALSE'}:
                stack.append((token, token == 'TRUE'))
            elif token in self.operators:
                if token == 'NOT':
                    a_expr, a_val = stack.pop()
                    result = self.operators[token].func(a_val)
                    results.append((f"~{a_expr}", result))
                    stack.append((f"~{a_expr}", result))
                else:
                    b_expr, b_val = stack.pop()
                    a_expr, a_val = stack.pop()
                    operator_symbol = {
                        'AND': '^',
                        'OR': 'v',
                        'IMPLIES': '->',
                        'IFF': '<->'
                    }.get(token, token)
                    result = self.operators[token].func(a_val, b_val)
                    results.append((f"{a_expr} {operator_symbol} {b_expr}", result))
                    stack.append((f"{a_expr} {operator_symbol} {b_expr}", result))
            else:
                raise ValueError(f"Unknown token: {token}")
        
        if len(stack) != 1:
            raise ValueError("Invalid postfix expression")
        return stack[0][1], results

    def create_truth_table(self, expression):
        tokens = self.tokenize_expression(expression)
        vars_in_expr = sorted(self.variables_set.intersection(token for token in tokens if token in self.variables_set))
        combinations = list(itertools.product([False, True], repeat=len(vars_in_expr)))

        if not combinations:
            print("No variables found in the expression.")
            return False
        
        initial_values = dict(zip(vars_in_expr, combinations[0]))
        sub_expressions = []

        try:
            _, sub_expressions = self.evaluate_postfix_expression(self.convert_to_postfix(tokens), initial_values)
        except Exception as e:
            print(f"Error during evaluation: {e}")
            return False
        
        headers = vars_in_expr + list(dict.fromkeys(sub_expr[0] for sub_expr in sub_expressions))

        # Calculate the maximum length of headers for alignment
        max_length = max(len(header) for header in headers)

        # Print headers with centering
        print('\n' + '─' * (max_length * len(headers) + 3 * (len(headers) - 1)))
        print(' | '.join(header.center(max_length) for header in headers))
        print('─' * (max_length * len(headers) + 3 * (len(headers) - 1)))

        tautology = True
        for combo in combinations:
            values = dict(zip(vars_in_expr, combo))
            try:
                final_result, intermediate = self.evaluate_postfix_expression(self.convert_to_postfix(tokens), values)
                sub_results = {sub: res for sub, res in intermediate}
            except ValueError as ve:
                print(f"Error evaluating expression: {ve}")
                return False

            row = ' | '.join(('TRUE' if values[var] else 'FALSE').center(max_length) for var in vars_in_expr)
            for sub in headers[len(vars_in_expr):]:
                res = sub_results.get(sub, False)
                row += ' | ' + ('TRUE' if res else 'FALSE').center(max_length)
            print(row)
            if not final_result:
                tautology = False
            
        return tautology

    def read_statements_from_file(self, file_path):
        try:
            with open(file_path, 'r') as file:
                statements = [line.strip().upper() for line in file if line.strip()]
            return statements
        except FileNotFoundError:
            print(f"Error: File '{file_path}' not found.")
            return []
        except Exception as e:
            print(f"Error reading file: {e}")
            return []

def print_menu():
    menu = (
        "═" * 232 + "\n"
        "Choose an option:\n"
        "1. Read logical statements from a file\n"
        "2. Enter a logical statement\n"
        "3. Exit\n"
        "Enter your choice (1/2/3): "
    )
    print(menu, end='')  # Keep the cursor on the same line for input

def main_program():
    parser = LogicExpressionParser()
    print("═" * 232)
    print("\t\t\t\t\t\t\t\t\t\t\t\t\t   TRUTH TABLE GENERATOR")
    print("\t\t\t\t\t\t\t\t\t\t\t\t\t\t  WELCOME!")
    print("\t\t\t\t\t\t\t\t\t\t\t\t\t    Use the variables P, Q, R")
    print("\t\t\t\t\t\t\t\t\t\t\t\t\tLogical Operators: ~, ^, or, ->, <->")
    
    while True:
        print_menu()
        choice = input().strip()

        if choice == '1':
            file_path = 'statement.txt'
            statements = parser.read_statements_from_file(file_path)
            if statements:
                for expression in statements:
                    print("═" * 232)
                    print(f"\nEvaluating logical statement: {expression}")
                    try:
                        tokens = parser.tokenize_expression(expression)
                        vars_in_expr = {token for token in tokens if token in parser.variables_set}
                        if not vars_in_expr:
                            print("Error: No valid variables (P, Q, R) found in the statement.")
                            continue  
                    except ValueError as ve:
                        print(f"Error in tokenizing expression: {ve}")
                        continue  
                    
                    print("Truth Table:")
                    parser.create_truth_table(expression)
        
        elif choice == '2':
            print("═" * 232)
            expression = input("\nEnter your logical statement: ").strip().upper()
            if not expression:
                print("Error: No logical statement provided. Please try again.")
                continue 
        
            try:
                tokens = parser.tokenize_expression(expression)
                vars_in_expr = {token for token in tokens if token in parser.variables_set}
                if not vars_in_expr:
                    print("Error: No valid variables (P, Q, R) found in the statement.")
                    continue  
            except ValueError as ve:
                print(f"Error in tokenizing expression: {ve}")
                continue  
            
            print("Truth Table:")
            parser.create_truth_table(expression)

        elif choice == '3':
            print("═" * 232)
            print("\t\t\t\t\t\t\t\t\t\t\t\t\tExiting the Truth Table Generator. Goodbye!")
            print("═" * 232)
            print("Developers: \n\tCabie, Lowell Augusteen\n\tMaramba, Loraine Mae\n\tPagurayan, Angel Lyka\n\tVerdadero, Guiller Rey")
            print("═" * 232)
            print()
            break

        else:
            print("Invalid choice. Please try again.")

if __name__ == "__main__":
    main_program()
