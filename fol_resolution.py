import copy
import time


class Predicate:
    def __init__(self, neg, name, args):
        self.name = name
        self.neg = neg
        self.args = args

    def negate(self):
        self.neg = not self.neg

    def makePredicate(predString):
        neg = False
        if predString[0] == "~":
            neg = True
        if neg:
            temp = predString[1:-1].split("(")
        else:
            temp = predString[:-1].split("(")
        name = temp[0]
        args = temp[1].split(",")
        for i in range(len(args)):
            if Predicate.isVariable(args[i]):
                if args[i] in Sentence.map:
                    args[i] = Sentence.map[args[i]]
                else:
                    Sentence.map[args[i]] = "var" + str(Sentence.vCounter)
                    args[i] = Sentence.map[args[i]]
                    Sentence.vCounter += 1

        return Predicate(neg, name, args)

    def __str__(self):
        neg = ""
        if self.neg:
            neg = "~"
        arg = ""
        for each in self.args:
            arg += each + ","
        arg = arg[:-1]
        return neg + self.name + "(" + arg + ")"

    def isVariable(x):
        if x[0].islower():
            return True
        return False

    def canUnify(self, p):
        for i in range(len(self.args)):
            if (not Predicate.isVariable(self.args[i])) and (not Predicate.isVariable(p.args[i])) and self.args[i] != \
                    p.args[i]:
                return False
        return True

    def canCancel(self, p):
        if self.name == p.name and self.neg != p.neg:
            if self.canUnify(p):
                return True
        return False

    def unify(p1, p2):
        map = {}
        flag = False
        for i in range(len(p1.args)):
            if Predicate.isVariable(p1.args[i]) and Predicate.isVariable(p2.args[i]):
                map[p1.args[i]] = p2.args[i]
            elif not Predicate.isVariable(p1.args[i]) and Predicate.isVariable(p2.args[i]):
                map[p2.args[i]] = p1.args[i]
                flag = True
            elif not Predicate.isVariable(p2.args[i]) and Predicate.isVariable(p1.args[i]):
                map[p1.args[i]] = p2.args[i]
                flag = True
            elif not Predicate.isVariable(p2.args[i]) and not Predicate.isVariable(p1.args[i]) and p1.args[i] == \
                    p2.args[i]:
                map[p1.args[i]] = p2.args[i]
                flag = True
            elif not Predicate.isVariable(p2.args[i]) and not Predicate.isVariable(p1.args[i]) and not (
                    p1.args[i] == p2.args[i]):
                flag = False
                break
        if not flag:
            map.clear()
        return map

    def same(self, other):
        if (self.name != other.name):
            return False
        if (len(self.args) != len(other.args)):
            return False
        for i in range(len(self.args)):
            if self.args[i] != other.args[i]:
                return False
        return True

    def __eq__(self, other):
        if self.neg != other.neg:
            return False
        if (self.name != other.name):
            return False
        if (len(self.args) != len(other.args)):
            return False
        for i in range(len(self.args)):
            if (not Predicate.isVariable(self.args[i])) and (not Predicate.isVariable(other.args[i])) and self.args[i] != other.args[i]:
                return False
        return True




class Sentence:
    map = dict()
    vCounter = 0

    def __init__(self, predicates):
        self.predicates = predicates

    def makeSentence(sentString):
        predicates = list()
        if "=>" in sentString:
            temp = sentString.split("=>")
            left = temp[0].split("&")
            for each in left:
                p = Predicate.makePredicate(each)
                p.negate()
                predicates.append(p)
            right = Predicate.makePredicate(temp[1])
            predicates.append(right)
        else:
            predicates.append(Predicate.makePredicate(sentString))
        Sentence.map.clear()
        return Sentence(predicates)

    def __str__(self):
        s = "["
        for each in self.predicates:
            s += str(each) + ","
        s = s[:-1]
        s += "]"
        return s

    def negateSentence(self):
        for i in range(len(self.predicates)):
            self.predicates[i].negate()

    def canResolve(self, s):
        for each in self.predicates:
            for other in s.predicates:
                if each.canCancel(other):
                    return True

        return False

    def getPossibleClauses(self, kb):
        clauses = list()
        for each in kb:
            if self.canResolve(each):
                clauses.append(each)
        return clauses

    def getSubstitution(self, s):
        subs = list()
        for p1 in self.predicates:
            for p2 in s.predicates:
                if p1.name == p2.name:
                    map = Predicate.unify(p1, p2)
                    if len(map):
                        subs.append(map)
        return subs

    def substitute(p, p2, sub):
        inference = []
        p0 = []
        p1 = []
        for each in p.predicates:
            args = []
            for i in range(len(each.args)):
                if each.args[i] in sub and Predicate.isVariable(each.args[i]):
                    args.append(sub[each.args[i]])
                else:
                    args.append(each.args[i])
            p0.append(Predicate(each.neg, each.name, args))

        for each in p2.predicates:
            args = []
            for i in range(len(each.args)):
                if each.args[i] in sub and Predicate.isVariable(each.args[i]):
                    args.append(sub[each.args[i]])
                else:
                    args.append(each.args[i])
            p1.append(Predicate(each.neg, each.name, args))

        for x in p0:
            flag = False
            for o in p1:
                if x.same(o) and x.neg != o.neg:
                    flag = True
                    break
            if not flag:
                inference.append(x)

        for x in p1:
            flag = False
            for o in p0:
                if x.same(o) and x.neg != o.neg:
                    flag = True
                    break
            if not flag:
                inference.append(x)

        if len(inference) == 0:
            inference.append(Predicate(False, "TRUE", []))

        return Sentence(inference)

    def resolve(self, clause):
        inferences = list()
        substitutions = self.getSubstitution(clause)
        # print(str(self)+"----"+str(clause))
        # print(substitutions)
        for each in substitutions:
            s = Sentence.substitute(self, clause, each)
            # print(s)
            # print(self)
            inferences.append(s)
            # print(inferences)
        return inferences


class homework:
    def __init__(self):
        self.KB = list()
        self.Queries = list()
        self.nKB = 0
        self.nQ = 0
        self.starttime = time.time()

    def processInput(self, filePath):
        """
        Parses input to form KB,
        :param filePath: input file path
        :return: Does not return
        """
        f = open(filePath, "r")
        lines = f.readlines()
        self.nQ = int(lines[0])
        for i in range(1, 1 + self.nQ):
            l = lines[i].strip().replace(" ", "").replace("\t", "")
            self.Queries.append(Sentence.makeSentence(l))
            # print("----------------------------------")
        self.nKB = int(lines[1 + self.nQ])
        for i in range(2 + self.nQ, 2 + self.nQ + self.nKB):
            l = lines[i].strip().replace(" ", "").replace("\t", "")
            self.KB.append(Sentence.makeSentence(l))
        # print("Queries")
        # homework.printSent(self.Queries)
        # print("KB")
        # homework.printSent(self.KB)
        # print("--------------------------------")

    def start(self):
        """
        Executes workflow
        :return: Does not return
        """
        # print("--------------------------------")
        f = open("output.txt",'w')
        for each in self.Queries:
            testKB = copy.copy(self.KB)
            result = self.ask(testKB, each)
            print(result)
            if result:
                f.write("TRUE\n")
            else:
                f.write("FALSE\n")
            # print("=========================================================")

    def ask(self, kb, query):
        """
        This function checks if the KB entails the query by resolution
        :param kb: Copy of original KB (List of Sentences)
        :param query: alpha query (Sentence)
        :return: True/False
        """
        self.starttime = time.time()
        tempq = copy.copy(query)
        tempq.negateSentence()
        kb.append(tempq)
        # print("---------------TEST------------------")
        # homework.printSent(kb)
        # print("-----------------------------------")
        kb.sort(key=lambda x: len(x.predicates))
        while True:
            if time.time()-self.starttime>10:
                break
            newKnowledge = list()
            for each in kb:
                if time.time() - self.starttime > 10:
                    break
                # delta = time.time()- starttime
                # if delta >= 55:
                #     return False
                # print("kb_sent:" + str(each))
                clauses = each.getPossibleClauses(kb)
                for clause in clauses:
                    if time.time() - self.starttime > 10:
                        break
                    # delta = time.time() - starttime
                    # if delta >= 55:
                    #     return False
                    # print(each,clause)
                    resolvants = each.resolve(clause)
                    for x in resolvants:
                        if len(x.predicates) == 1 and x.predicates[0].name == "TRUE":
                            return True
                    # print(each)
                    newKnowledge += resolvants
                    # print("++++++++++++++++++++")
                if time.time() - self.starttime > 10:
                    break
                # print("--------------------------------")
            if time.time()-self.starttime>10:
                break
            newKnowledgeNoDups = self.removeDups(newKnowledge)
            if time.time()-self.starttime>10:
                break
            # print("--------------NEW KNOW---------------")
            # homework.printSent(newKnowledgeNoDups)
            if len(newKnowledgeNoDups) == 0:
                # print("Genuine")
                break
            diff = self.difference(kb, newKnowledgeNoDups)
            if time.time()-self.starttime>10:
                break
            # print("-------------DIFF---------------")
            # homework.printSent(diff)
            if len(diff) == 0:
                # print("Genuine")
                break
            kb += diff
            kb.sort(key=lambda x: len(x.predicates))
            # print("-------------KB-----------------")
            # homework.printSent(kb)
            # input()
        return False

    def removeDups(self, k):
        """
        This function removes duplicate infered sentences
        :param k: list of sentences
        :return: list of sentences without duplicates
        """
        remove = []
        for i in range(len(k) - 1):
            p0 = k[i].predicates
            for j in range(i + 1, len(k)):
                if time.time() - self.starttime > 10:
                    break
                p1 = k[j].predicates
                if self.matchPredList(p0,p1):
                    remove.append(j)
            if time.time()-self.starttime>10:
                break
        nodups = []
        for i in range(len(k)):
            if i not in remove:
                nodups.append(k[i])

        return nodups


    def difference(self, kb, inferences):
        """
        Returns sentences from inference not in kb
        :param kb: List of Sentences
        :param inferences: List of Sentences
        :return: List of Sentence (inference-kb)
        """
        diff = []
        for each in inferences:
            p0 = each.predicates
            flag = False
            for other in kb:
                if time.time() - self.starttime > 10:
                    break
                p1 = other.predicates
                if self.matchPredList(p0,p1):
                    flag = True
                    break
            if time.time()-self.starttime>10:
                break
            if not flag:
                diff.append(each)
        return diff

    def matchPredList(self,p1,p2):
        match = []
        flag1 = False
        for each in p1:
            for other in p2:
                if time.time() - self.starttime > 10:
                    break
                if each == other:
                    match.append(each)
                    break
            if time.time()-self.starttime>10:
                break
        if len(match) == len(p1):
            flag1 = True
        match = []
        flag2 = False
        for each in p2:
            for other in p1:
                if time.time() - self.starttime > 10:
                    break
                if each == other:
                    match.append(each)
                    break
            if time.time()-self.starttime>10:
                break

        if len(match) == len(p2):
            flag2 = True
        return flag1 and flag2

    def printSent(listSentences):
        for each in listSentences:
            print(each)


def main():
    h = homework()
    h.processInput("input_46.txt")
    h.start()


if __name__ == "__main__":
    main()
