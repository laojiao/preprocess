#!/usr/bin/env python
# Copyright (c) 2002-2008 ActiveState Software Inc.
# License: MIT License (http://www.opensource.org/licenses/mit-license.php)

# This is modified to deal with C project, with preprocess command not in comment.
# Options are removed.
# The output is for call tree analysis, not to be built.
# How to use:
#  Set the variable workplace, and run this file.

from builtins import str
from builtins import range

import os
import sys
import re

class PreprocessError(Exception):
    def __init__(self, errmsg, file=None, lineno=None, line=None):
        self.errmsg = str(errmsg)
        self.file = file
        self.lineno = lineno
        self.line = line
        Exception.__init__(self, errmsg, file, lineno, line)
    def __str__(self):
        s = ""
        if self.file is not None:
            s += self.file + ":"
        if self.lineno is not None:
            s += str(self.lineno) + ":"
        if self.file is not None or self.lineno is not None:
            s += " "
        s += self.errmsg
        #if self.line is not None:
        #    s += ": " + self.line
        return s

#---- internal support stuff
# This function is especially modified to eval directly C language.

def _evaluate(expr, defines):
    expr = expr.replace("||","|") # Replace logic operators.
    expr = expr.replace("&&","&")
    expr = expr.replace("!defined", "ndefined") # Deal with !.
    expr = expr.replace("! defined", "ndefined")
    expr = re.sub("(\s*/\*.*\*/\s*)","",expr) # Get rid of comment
    
    # Add '' around the variable.(This may solve the problem for the original project too?)
    rule = re.compile("defined\s*[(]\s*([a-zA-Z_]+[a-zA-Z0-9_]*)\s*[)]")
    match = rule.search(expr)
    if match:
        expr = re.sub(rule,"defined ( '\g<1>' )",expr)
    
    try:
        rv = eval(expr, {'defined':lambda v: v in defines,'ndefined':lambda v: v not in defines}, defines)
    except Exception as ex:
        msg = str(ex)
        print(expr, msg)
        sys.exit()
    return rv


#---- module API

def preprocess(workspace, infile, outfile=sys.stdout, defines={},
               force=0, keepLines=0, includePath=[],
               substitute=0, include_substitute=0):
    if isinstance(infile, tuple):
        infile, from_, to_, last_to_line = infile
    else:
        from_, to_, last_to_line = None, None, None

    # Patterns are modified to fit my own use.
    # No need for comment patterns according to file type so removed.
    stmts = ['\s*#\s*(?P<op>if|elif|ifdef|ifndef)\s+(?P<expr>.*)$',
             '\s*#\s*(?P<op>else|endif)(\s*/\*.*\*/\s*)?\s*$',
             '\s*#\s*(?P<op>error)\s+(?P<error>.*?)(\s*/\*.*\*/\s*)?$',
             '\s*#\s*(?P<op>define)\s+(?P<var>[\S]*)\s*[( ]?(\s?(?P<val>\S+))?[ )]?\s*(/*.*)?(\s*/\*.*\*/\s*)?$',
             '\s*#\s*(?P<op>undef)\s+(?P<var>[\S]*?)',
             '\s*#\s*(?P<op>include) +"(?P<fname>.*?)" +(?P<fromto>fromto_?):\s+(?P<part>.+\n)',
             '\s*#\s*(?P<op>include)\s+"(?P<fname>.*?)"',
             r'\s*#\s*(?P<op>include)\s+(?P<var>[\S]+?)',
            ]
    stmtRes = [re.compile(p) for p in stmts]

    # Process the input file.
    # (Would be helpful if I knew anything about lexing and parsing
    # simple grammars.)
    fin = open(infile, 'r')
    lines = fin.readlines()
    if from_ is not None:
        from_line = -1
        to_line = -1
        for i in range(len(lines)):
            if re.search(from_, lines[i]):
                from_line = i
            if to_ != '' and from_line != -1:
                # not to end of file and has found from_ line
                if re.search(to_, lines[i]):
                    to_line = i if last_to_line else i-1
                    break
        if to_line == -1:
            lines = lines[from_line:]
        else:
            lines = lines[from_line:to_line+1]

    fin.close()
    if isinstance(outfile, (str, bytes)):
        if force and os.path.exists(outfile):
            os.chmod(outfile, 0o777)
            os.remove(outfile)
        fout = open(outfile, 'w')
    else:
        fout = outfile

    defines['__FILE__'] = infile
    SKIP, EMIT = range(2) # states
    states = [(EMIT,   # a state is (<emit-or-skip-lines-in-this-section>,
               0,      #             <have-emitted-in-this-if-block>,
               0)]     #             <have-seen-'else'-in-this-if-block>)
    lineNum = 0
    for line in lines:
        lineNum += 1
        defines['__LINE__'] = lineNum

        # Get rid of the 'u' after numbers meaning unsigned.
        popu = re.compile("([0-9])u")
        pop = popu.search(line)
        if pop:
            line = re.sub(popu,"\g<1>",line)

        # Is this line a preprocessor stmt line?
        #XXX Could probably speed this up by optimizing common case of
        #    line NOT being a preprocessor stmt line.
        for stmtRe in stmtRes:
            match = stmtRe.match(line)
            if match:
                break
        else:
            match = None

        if match:
            op = match.group("op")
            if op == "define":
                if not (states and states[-1][0] == SKIP):
                    var, val = match.group("var", "val")
                    if val is None:
                        val = None
                    else:
                        try:
                            val = eval(val, {}, {})
                        except:
                            pass
                    if val in defines:
                        defines[var] = defines[val] # Deal with assigning a value already exist as key(exp. #define VAR1 1 and then #define VAR2 VAR1)
                    else:
                        try:
                            defines[var] = eval(val) # Deal with value that still need calculation or hex numbers.(exp. #define VAR 2*2 or #define VAR 0x01)
                        except:
                            defines[var] = val
                fout.write(line) # Keep define lines
            elif op == "undef":
                if not (states and states[-1][0] == SKIP):
                    var = match.group("var")
                    try:
                        del defines[var]
                    except KeyError:
                        pass
            elif op == "include":
                if not (states and states[-1][0] == SKIP):
                    if "var" in match.groupdict():
                        # This is the second include form: #include VAR
                        var = match.group("var")
                        f = defines[var]
                    else:
                        # This is the first include form: #include "path"
                        f = match.group("fname")
                        fromto = part = None
                        if "fromto" in match.groupdict():
                            fromto, part = match.group("fromto", "part")
                            if fromto == 'fromto_':
                                last_to_line = True
                            else:
                                last_to_line = False
                            try:
                                from_, to_ = part.split('@')
                            except ValueError:
                                raise PreprocessError('Wrong syntax, need #include %s: from-regex@to-regex' % fromto)


                    # HPL modification:
                    # Perform substitutions here such that #include statements
                    # can use defines.
                    if include_substitute:
                        for name in reversed(sorted(defines, key=len)):
                            value = defines[name]
                            f = f.replace(name, str(value))

                    for root,di,file in os.walk(workspace):
                        fname = os.path.normpath(os.path.join(root, f))
                        if os.path.exists(fname):
                            break
                    else:
                        raise PreprocessError("could not find #include'd file "\
                                              "\"%s\" on include path: %r"\
                                              % (f, includePath))
                    if fromto is not None:
                        fname = (fname, from_, to_, last_to_line)
                    defines = preprocess(workspace, fname, fout, defines, force,
                                         keepLines, includePath,
                                         substitute, include_substitute)
                fout.write(line) # Keep define lines
            elif op in ("if", "ifdef", "ifndef"):
                if op == "if":
                    expr = match.group("expr")
                elif op == "ifdef":
                    expr = "defined('%s')" % match.group("expr")
                elif op == "ifndef":
                    expr = "not defined('%s')" % match.group("expr")
                try:
                    if states and states[-1][0] == SKIP:
                        # Were are nested in a SKIP-portion of an if-block.
                        states.append((SKIP, 0, 0))
                    else:
                        bol = _evaluate(expr, defines)
                        if bol:
                            states.append((EMIT, 1, 0))
                        else:
                            states.append((SKIP, 0, 0))
                except KeyError:
                    raise PreprocessError("use of undefined variable in "\
                                          "#%s stmt" % op, defines['__FILE__'],
                                          defines['__LINE__'], line)
            elif op == "elif":
                expr = match.group("expr")
                try:
                    if states[-1][2]: # already had #else in this if-block
                        raise PreprocessError("illegal #elif after #else in "\
                            "same #if block", defines['__FILE__'],
                            defines['__LINE__'], line)
                    elif states[-1][1]: # if have emitted in this if-block
                        states[-1] = (SKIP, 1, 0)
                    elif states[:-1] and states[-2][0] == SKIP:
                        # Were are nested in a SKIP-portion of an if-block.
                        states[-1] = (SKIP, 0, 0)
                    else:
                        bol = _evaluate(expr, defines)
                        if bol:
                            states[-1] = (EMIT, 1, 0)
                        else:
                            states[-1] = (SKIP, 0, 0)
                except IndexError:
                    raise PreprocessError("#elif stmt without leading #if "\
                                          "stmt", defines['__FILE__'],
                                          defines['__LINE__'], line)
            elif op == "else":
                try:
                    if states[-1][2]: # already had #else in this if-block
                        raise PreprocessError("illegal #else after #else in "\
                            "same #if block", defines['__FILE__'],
                            defines['__LINE__'], line)
                    elif states[-1][1]: # if have emitted in this if-block
                        states[-1] = (SKIP, 1, 1)
                    elif states[:-1] and states[-2][0] == SKIP:
                        # Were are nested in a SKIP-portion of an if-block.
                        states[-1] = (SKIP, 0, 1)
                    else:
                        states[-1] = (EMIT, 1, 1)
                except IndexError:
                    raise PreprocessError("#else stmt without leading #if "\
                                          "stmt", defines['__FILE__'],
                                          defines['__LINE__'], line)
            elif op == "endif":
                try:
                    states.pop()
                except IndexError:
                    raise PreprocessError("#endif stmt without leading #if"\
                                          "stmt", defines['__FILE__'],
                                          defines['__LINE__'], line)
            elif op == "error":
                if not (states and states[-1][0] == SKIP):
                    error = match.group("error")
                    raise PreprocessError("#error: "+error, defines['__FILE__'],
                                          defines['__LINE__'], line)
            if keepLines:
                fout.write("\n")
        else:
            try:
                if states[-1][0] == EMIT:
                    sline = line
                    if substitute:
                        for name in reversed(sorted(defines, key=len)):
                            value = defines[name]
                            sline = sline.replace(name, str(value))
                    fout.write(sline)
                elif keepLines:
                    fout.write("\n")
            except IndexError:
                raise PreprocessError("superfluous #endif before this line",
                                      defines['__FILE__'],
                                      defines['__LINE__'])
    if len(states) > 1:
        raise PreprocessError("unterminated #if block", defines['__FILE__'],
                              defines['__LINE__'])
    elif len(states) < 1:
        raise PreprocessError("superfluous #endif on or before this line",
                              defines['__FILE__'], defines['__LINE__'])
    if fout != outfile:
        fout.close()
    
    return defines


#---- mainline

def main():
    workspace = r"D:\master" #Local directory to define as target input.
    defines = {}
    for r,d,f in os.walk(workspace):
        for file in f:
            # Only take .c and .h as target.
            if file[-2:] in [".c", ".h"]:
                infile = os.path.join(r,file)
                # Default output directory is a folder named 'output' under the same root as the workspace folder.
                outfile = os.path.join(workspace[:workspace.rindex("\\")+1],"output",r[len(workspace)+1:],file)
                preprocess(workspace, infile, outfile, defines, 1)


if __name__ == "__main__":
    sys.exit( main() )
