# Patrick Drummond
# 40185198
# COMP 5361
# March 10, 2021


# Test Inputs from passgn2.pdf
testSentence1 = "((P1 AND P2) OR (P3 AND True)) OR ((~P1 AND ~P3) AND P2)"
testSentence2 = "(~P1 AND (P1 OR P2)) IMPLIES P2"
testSentence3 = "P2 AND (P1 IMPLIES ~P2) AND (~P1 IMPLIES ~P2)"
testSentence4 = "(P1 IMPLIES (P2 IMPLIES P3)) IMPLIES ((P1 IMPLIES P2) IMPLIES P3)"

# Operators and P Values
OPERATORS = ['and', 'or', 'implies', "not"]
PVALUES = ['True', 'False']


# Deterine the number of variables that need assignment
def get_variable_count(sentence):
    variables = 0
    for i in range(0, len(sentence)):
        variable = "P" + str(i)
        if variable in sentence:
            variables += 1
    return variables


# Replace variables with user values
def assign_variable_value(sentence):
    variable_count = get_variable_count(sentence)
    for i in range(0, variable_count):
        sv = "P" + str(i+1)
        uv = input("Assign value to " + sv + ": Use 'T' or 'F' >> ")
        if uv == "T":
            sentence = sentence.replace(sv, "True")
        if uv == "F":
            sentence = sentence.replace(sv, "False")

    return sentence


# Convert sentence from string to list
def convert_to_list(sentence):

    pDict = []
    index = 0

    for i in range(0, len(sentence)):
        if sentence[i] == "(":
            pDict.append("(")
            index += 1
        if sentence[i] == ")":
            pDict.append(")")
            index += 1
        if sentence[i] == "T":
            pDict.append("True")
            index += 1
        if sentence[i] == "F":
            pDict.append("False")
            index += 1
        if sentence[i] == "O":
            pDict.append("or")
            index += 1
        if sentence[i] == "A":
            pDict.append("and")
            index += 1
        if sentence[i] == "~":
            pDict.append("not")
            index += 1
        if sentence[i] == "M":
            pDict.append("implies")
            index += 1

    # Fixing bug where boolean eval is wrong if the sentence doesn't start and end with parenthesis
    # Check if first item in list is '(', if not, insert it
    if pDict[0] != '(':
        pDict.insert(0, "(")
        pDict.append(")")

    return pDict


# Switch 'not Pvalue' to opposite value
def convert_negations(sentenceList):

    # Iterate through sentence looking for a 'not' followed by a p value
    for i in range(0, len(sentenceList)):
        if sentenceList[i] in PVALUES and sentenceList[i - 1] == "not":
            # Replace P value with it's negation
            if sentenceList[i] == "True":
                sentenceList[i] = "False"
                continue
            if sentenceList[i] == "False":
                sentenceList[i] = "True"
                continue

    # Remove the 'not' from the list completely
    res = [i for i in sentenceList if i != "not"]

    return res


# Logic Gates for applying boolean logic
def logic_gate(p1, p2, type):

    # Convert variables from string to boolean
    if p1 == ("False"):
        p1 = False
    if p2 == ("False"):
        p2 = False

    if p1 == ("True"):
        p1 = True
    if p2 == ("True"):
        p2 = True

    # Boolean logic gates
    if type == ("and"):
        return str(p1 and p2)
    if type == ("or"):
        return str(p1 or p2)

    # Implies Logic Gate
    if type == ("implies"):
        if p1 is True and p2 is False:
            return 'False'
        return 'True'


# Convert list of sentence items from infix to postfix
def intoPost(infix):

    stack = []
    postfixList = []

    # Iterate over expression for conversion
    for i in range(0, len(infix)):
        cc = infix[i]

        # If operator push to stack
        if cc in OPERATORS:
            stack.append(cc)
            # print("Stack: ", stack)

        # If item is a value, add to output
        elif cc in PVALUES:
            postfixList.append(cc)

        # If item is '(' push it to stack
        elif cc == "(":
            stack.append(cc)

        # If character is ')', pop and output from stack until '(' is found
        elif cc == ")":
            # While stack is not empty and stack.peek is not a open parenthesis
            # Pop from stack and add it to postfix statement
            while stack[-1] != '(':
                a = stack.pop()
                # print("A: ", a)
                postfixList.append(a)
            if (stack == True) and stack[-1] != '(':
                return -1
            else:
                stack.pop()

    # Last 'or' isn't getting pushed...
    # Check stack for contents, if found simply add to end of postfix
    if (stack):
        a = stack.pop()
        postfixList.append(a)

    # Debug print functions
    # print("Final Stack: ", stack)
    # print("PostFix: ", postfixList)

    return postfixList


# Evaluate the postfix expression
def evalPost(postfix):

    # Create a list to serve as our stack
    stack = []

    # Iterate through input list
    for i in range(0, len(postfix)):
        cc = postfix[i]

        # If item is value push it to stack
        if cc in PVALUES:
            stack.append(cc)

        # If item is an operator (logic gate) then pop 2 elements from stack and apply
        if cc in OPERATORS:
            val1 = stack.pop()
            val2 = stack.pop()
            # Note: Switching val1 and val2 input order to fix IMPLIES bug
            val3 = logic_gate(val2, val1, cc)
            # print("Adding to Stack: ", val2, " : ", val1, " : ", cc, " : ", val3)
            stack.append(val3)
            # print("Stack is now: ", stack, "\n")

    return stack


# Method to evaluate sentence
# Input: string with assigned variables
# Return: string with boolean value of sentence
def evaluate_sentence(asv):
    asvList = convert_to_list(asv)
    asvList = convert_negations(asvList)
    postfix = intoPost(asvList)
    final_value = evalPost(postfix)

    if 'True' in final_value:
        return 'True'
    return 'False'


# Method to determine tautology, contingency, contradiciton
# Input is a list with truth table evaluations
# Output is a string
def determine_taut(tt_list):

    # Check to see what the list contains, output respective label
    if 'True' in tt_list:
        if 'False' in tt_list:
            return "Contingency"
        return "Tautology"
    return "Contradiction"


# Method to run Part 1 of assignment in total
def runPart1():

    # Ask user whether theyd like to run the test sentence or input their own test
    print("Enter '1' to run the supplied test input.")
    print("Enter '2' to run a custom input.")
    selection = input(">> ")

    if selection == '1':
        sentence = testSentence1
        print("Your sentence is: \n" + sentence)
        print("\nYour sentence requires " + str(get_variable_count(sentence)) + " assigned values:")
        asv = assign_variable_value(sentence)
        print("\nYour new sentence with variables assigned is: \n" + asv)
        asv_eval = evaluate_sentence(asv)
        print("\nYour Sentence Evaluates to: " + str(asv_eval) + ".")

    if selection == '2':
        sentence = input("Enter your custom input >>")
        print("Your sentence is: \n" + sentence)
        print("\nYour sentence requires " + str(get_variable_count(sentence)) + " assigned values:")
        asv = assign_variable_value(sentence)
        print("\nYour new sentence with variables assigned is: \n" + asv)
        asv_eval = evaluate_sentence(asv)
        print("\nYour Sentence Evaluates to: " + str(asv_eval) + ".")


# Draw a truth table
# Input is a sentence with unassigned variabled
# Output is visual truth table and sentence evaluation
def draw_truth_table(sentence):

    # Determine how many unassigned variables are in the sentence
    # Determine how many truth table cases you need
    variableCount = get_variable_count(sentence)
    cases = 2 ** variableCount

    print("\nSentence: ", sentence)
    print("\nTRUTH TABLE")

    # Print Head of truth table
    for i in range(0, variableCount):
        label = str(i + 1)
        print("| P" + label + "", end=" ")
        if i == variableCount - 1:
            print("| Evaluation |")

    # Print Contents of truth table for 4
    if cases == 4:
        # Display Truth Table for user
        print("------------------------")
        print("|  F |  F |    " + evaluate_sentence(assign_variable_auto(sentence, 0)))
        print("|  T |  F |    " + evaluate_sentence(assign_variable_auto(sentence, 1)))
        print("|  F |  T |    " + evaluate_sentence(assign_variable_auto(sentence, 2)))
        print("|  T |  T |    " + evaluate_sentence(assign_variable_auto(sentence, 3)))

        # Place boolean evaluations in a list to be used for tautology judgement
        tt_outList = []
        for i in range(0, cases):
            tt_value = evaluate_sentence(assign_variable_auto(sentence, i))
            tt_outList.append(tt_value)

    # Print Contents of truth table for 8
    if cases == 8:
        print("-----------------------------")
        print("|  F |  F |  F | " + evaluate_sentence(assign_variable_auto(sentence, 0)))
        print("|  F |  T |  F | " + evaluate_sentence(assign_variable_auto(sentence, 1)))
        print("|  F |  F |  T | " + evaluate_sentence(assign_variable_auto(sentence, 2)))
        print("|  F |  T |  T | " + evaluate_sentence(assign_variable_auto(sentence, 3)))
        print("|  T |  F |  F | " + evaluate_sentence(assign_variable_auto(sentence, 4)))
        print("|  T |  T |  F | " + evaluate_sentence(assign_variable_auto(sentence, 5)))
        print("|  T |  F |  T | " + evaluate_sentence(assign_variable_auto(sentence, 6)))
        print("|  T |  T |  T | " + evaluate_sentence(assign_variable_auto(sentence, 7)))

        tt_outList = []
        for i in range(0, cases):
            tt_value = evaluate_sentence(assign_variable_auto(sentence, i))
            tt_outList.append(tt_value)

    # Determine if TT values are a tautology etc
    # print(tt_outList)
    label = determine_taut(tt_outList)
    print("\nThis Sentence is a ", label)


# Method to run part 2 of assignment in total
def runPart2():
    # Ask user whether theyd like to run the test sentence or input their own test
    print("Enter '1' to run one of the supplied test input.")
    print("Enter '2' to run a custom input.")
    selection = input(">> ")

    if selection == "1":
        print("Enter '1' to run test input 1")
        print("Enter '2' to run test input 2")
        print("Enter '3' to run test input 3")
        choice = input(">> ")

        if choice == '1':
            draw_truth_table(testSentence2)
        if choice == '2':
            draw_truth_table(testSentence3)
        if choice == '3':
            draw_truth_table(testSentence4)

    if selection == '2':
        sentence = input("Enter your custom input >> ")
        draw_truth_table(sentence)


# Automatically assign variables to a sentence
# "Index" refers to placement in truth table
def assign_variable_auto(sentence, index):

    # Index refers to row in truth table
    variable_count = get_variable_count(sentence)
    cases = 2 ** variable_count
    # Check how many cases there are
    if cases == 4:
            sv = "P1"
            sx = "P2"
            if index == 0:
                sentence = sentence.replace(sv, 'False')
                sentence = sentence.replace(sx, 'False')
            if index == 1:
                sentence = sentence.replace(sv, 'True')
                sentence = sentence.replace(sx, 'False')
            if index == 2:
                sentence = sentence.replace(sv, 'False')
                sentence = sentence.replace(sx, 'True')
            if index == 3:
                sentence = sentence.replace(sv, 'True')
                sentence = sentence.replace(sx, 'True')

    if cases == 8:
        sv = "P1"
        sx = "P2"
        sy = "P3"
        if index == 0:
            sentence = sentence.replace(sv, 'False')
            sentence = sentence.replace(sx, 'False')
            sentence = sentence.replace(sy, 'False')
        if index == 1:
            sentence = sentence.replace(sv, 'False')
            sentence = sentence.replace(sx, 'True')
            sentence = sentence.replace(sy, 'False')
        if index == 2:
            sentence = sentence.replace(sv, 'False')
            sentence = sentence.replace(sx, 'False')
            sentence = sentence.replace(sy, 'True')
        if index == 3:
            sentence = sentence.replace(sv, 'False')
            sentence = sentence.replace(sx, 'True')
            sentence = sentence.replace(sy, 'True')
        if index == 4:
            sentence = sentence.replace(sv, 'True')
            sentence = sentence.replace(sx, 'False')
            sentence = sentence.replace(sy, 'False')
        if index == 5:
            sentence = sentence.replace(sv, 'True')
            sentence = sentence.replace(sx, 'True')
            sentence = sentence.replace(sy, 'False')
        if index == 6:
            sentence = sentence.replace(sv, 'True')
            sentence = sentence.replace(sx, 'False')
            sentence = sentence.replace(sy, 'True')
        if index == 7:
            sentence = sentence.replace(sv, 'True')
            sentence = sentence.replace(sx, 'True')
            sentence = sentence.replace(sy, 'True')

    return sentence


# Driver to run the entire project
def run_full_project():

    driver = True
    print("Truth Table and Boolean Operator Assignments")

    # While loop to prompt the user for their choices
    while(driver):

        # Select which part of the assignment user would like to run
        print("\nEnter '1' to run Part 1 and assign custom truth assignments.")
        print("Enter '2' to run Part 2 and generate a truth table.")
        print("Enter '3' to exit.")

        choice = input(">> ")

        if choice == "1":
            runPart1()

        elif choice == "2":
            runPart2()

        elif choice == '3':
            print("Goodbye.")
            exit(0)

        else:
            print("\nInvalid Input, Please Try Again.")


# Run the full project
run_full_project()

