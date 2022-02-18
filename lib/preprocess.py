#!/usr/bin/env python
# Copyright (c) 2002-2008 ActiveState Software Inc.
# License: MIT License (http://www.opensource.org/licenses/mit-license.php)

# This is modified to deal with C project, with preprocess command not in comment.
# Options are removed.
# The output is for call tree analysis, not to be built.
# How to use:
#  Set the variable workplace, and run this file.

from past.builtins import cmp
from builtins import map
from builtins import str
from builtins import range
from builtins import object

import os
import sys
import getopt
import types
import re
import pprint

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

#---- internal logging facility

class _Logger(object):
    DEBUG, INFO, WARN, ERROR, CRITICAL = range(5)
    def __init__(self, name, level=None, streamOrFileName=sys.stderr):
        self._name = name
        if level is None:
            self.level = self.WARN
        else:
            self.level = level
        if type(streamOrFileName) == bytes:
            self.stream = open(streamOrFileName, 'w')
            self._opennedStream = 1
        else:
            self.stream = streamOrFileName
            self._opennedStream = 0
    def __del__(self):
        if self._opennedStream:
            self.stream.close()
    def getLevel(self):
        return self.level
    def setLevel(self, level):
        self.level = level
    def _getLevelName(self, level):
        levelNameMap = {
            self.DEBUG: "DEBUG",
            self.INFO: "INFO",
            self.WARN: "WARN",
            self.ERROR: "ERROR",
            self.CRITICAL: "CRITICAL",
        }
        return levelNameMap[level]
    def isEnabled(self, level):
        return level >= self.level
    def isDebugEnabled(self): return self.isEnabled(self.DEBUG)
    def isInfoEnabled(self): return self.isEnabled(self.INFO)
    def isWarnEnabled(self): return self.isEnabled(self.WARN)
    def isErrorEnabled(self): return self.isEnabled(self.ERROR)
    def isFatalEnabled(self): return self.isEnabled(self.FATAL)
    def log(self, level, msg, *args):
        if level < self.level:
            return
        message = "%s: %s: " % (self._name, self._getLevelName(level).lower())
        message = message + (msg % args) + "\n"
        self.stream.write(message)
        self.stream.flush()
    def debug(self, msg, *args):
        self.log(self.DEBUG, msg, *args)
    def info(self, msg, *args):
        self.log(self.INFO, msg, *args)
    def warn(self, msg, *args):
        self.log(self.WARN, msg, *args)
    def error(self, msg, *args):
        self.log(self.ERROR, msg, *args)
    def fatal(self, msg, *args):
        self.log(self.CRITICAL, msg, *args)

log = _Logger("preprocess", _Logger.WARN)
#log = _Logger("preprocess", _Logger.DEBUG)



#---- internal support stuff
# This function is especially modified to eval directly C language.

def _evaluate(expr, defines):
    """Evaluate the given expression string with the given context.
    WARNING: This runs eval() on a user string. This is unsafe.
    """
    #interpolated = _interpolate(s, defines)
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
    log.debug("evaluate %r -> %s (defines=%r)", expr, rv, defines)
    return rv


#---- module API

def preprocess(workspace, infile, outfile=sys.stdout, defines={},
               force=0, keepLines=0, includePath=[],
               substitute=0, include_substitute=0,
               contentType=None, contentTypesRegistry=None,
               __preprocessedFiles=None):
    if isinstance(infile, tuple):
        infile, from_, to_, last_to_line = infile
    else:
        from_, to_, last_to_line = None, None, None

    if __preprocessedFiles is None:
        __preprocessedFiles = []
    log.info("preprocess(infile=%r, outfile=%r, defines=%r, force=%r, "\
             "keepLines=%r, includePath=%r, contentType=%r, "\
             "__preprocessedFiles=%r)", infile, outfile, defines, force,
             keepLines, includePath, contentType, __preprocessedFiles)
    absInfile = os.path.normpath(os.path.abspath(infile))
    if absInfile in __preprocessedFiles:
        pass
        # Allow the same file to be included multiple times, it is not
        # necessarily recursive include!
        #raise PreprocessError("detected recursive #include of '%s'"\
        #                      % infile)
    __preprocessedFiles.append(os.path.abspath(infile))

    # Determine the content type and comment info for the input file.
    if contentType is None:
        contentType = "C++"

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
        log.debug("line %d: %r", lineNum, line)
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
            log.debug("%r stmt (states: %r)", op, states)
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
                                         substitute, include_substitute,
                                         contentTypesRegistry=contentTypesRegistry,
                                         __preprocessedFiles=__preprocessedFiles)
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
            log.debug("states: %r", states)
            if keepLines:
                fout.write("\n")
        else:
            try:
                if states[-1][0] == EMIT:
                    log.debug("emit line (%s)" % states[-1][1])
                    # Substitute all defines into line.
                    # XXX Should avoid recursive substitutions. But that
                    #     would be a pain right now.
                    sline = line
                    if substitute:
                        for name in reversed(sorted(defines, key=len)):
                            value = defines[name]
                            sline = sline.replace(name, str(value))
                    fout.write(sline)
                elif keepLines:
                    log.debug("keep blank line (%s)" % states[-1][1])
                    fout.write("\n")
                else:
                    log.debug("skip line (%s)" % states[-1][1])
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


#---- content-type handling

_gDefaultContentTypes = """
    C++                 .c       # C++ because then we can use //-style comments
    C++                 .cpp
    C++                 .cxx
    C++                 .cc
    C++                 .h
    C++                 .hpp
    C++                 .hxx
    C++                 .hh
"""

class ContentTypesRegistry(object):
    """A class that handles determining the filetype of a given path.
    Usage:
        >>> registry = ContentTypesRegistry()
        >>> registry.getContentType("foo.py")
        "Python"
    """

    def __init__(self, contentTypesPaths=None):
        self.contentTypesPaths = contentTypesPaths
        self._load()

    def _load(self):
        from os.path import dirname, join, exists

        self.suffixMap = {}
        self.regexMap = {}
        self.filenameMap = {}

        self._loadContentType(_gDefaultContentTypes)
        localContentTypesPath = join(dirname(__file__), "content.types")
        if exists(localContentTypesPath):
            log.debug("load content types file: `%r'" % localContentTypesPath)
            self._loadContentType(open(localContentTypesPath, 'r').read())
        for path in (self.contentTypesPaths or []):
            log.debug("load content types file: `%r'" % path)
            self._loadContentType(open(path, 'r').read())

    def _loadContentType(self, content, path=None):
        """Return the registry for the given content.types file.
        The registry is three mappings:
            <suffix> -> <content type>
            <regex> -> <content type>
            <filename> -> <content type>
        """
        for line in content.splitlines(0):
            words = line.strip().split()
            for i in range(len(words)):
                if words[i][0] == '#':
                    del words[i:]
                    break
            if not words: continue
            contentType, patterns = words[0], words[1:]
            if not patterns:
                if line[-1] == '\n': line = line[:-1]
                raise PreprocessError("bogus content.types line, there must "\
                                      "be one or more patterns: '%s'" % line)
            for pattern in patterns:
                if pattern.startswith('.'):
                    if sys.platform.startswith("win"):
                        # Suffix patterns are case-insensitive on Windows.
                        pattern = pattern.lower()
                    self.suffixMap[pattern] = contentType
                elif pattern.startswith('/') and pattern.endswith('/'):
                    self.regexMap[re.compile(pattern[1:-1])] = contentType
                else:
                    self.filenameMap[pattern] = contentType

    def getContentType(self, path):
        """Return a content type for the given path.
        @param path {str} The path of file for which to guess the
            content type.
        @returns {str|None} Returns None if could not determine the
            content type.
        """
        basename = os.path.basename(path)
        contentType = None
        # Try to determine from the path.
        if not contentType and basename in self.filenameMap:
            contentType = self.filenameMap[basename]
            log.debug("Content type of '%s' is '%s' (determined from full "\
                      "path).", path, contentType)
        # Try to determine from the suffix.
        if not contentType and '.' in basename:
            suffix = "." + basename.split(".")[-1]
            if sys.platform.startswith("win"):
                # Suffix patterns are case-insensitive on Windows.
                suffix = suffix.lower()
            if suffix in self.suffixMap:
                contentType = self.suffixMap[suffix]
                log.debug("Content type of '%s' is '%s' (determined from "\
                          "suffix '%s').", path, contentType, suffix)
        # Try to determine from the registered set of regex patterns.
        if not contentType:
            for regex, ctype in self.regexMap.items():
                if regex.search(basename):
                    contentType = ctype
                    log.debug("Content type of '%s' is '%s' (matches regex '%s')",
                              path, contentType, regex.pattern)
                    break
        # Try to determine from the file contents.
        content = open(path, 'rb').read()
        if content.startswith(b"<?xml"):  # cheap XML sniffing
            contentType = "XML"
        return contentType

_gDefaultContentTypesRegistry = None
def getDefaultContentTypesRegistry():
    global _gDefaultContentTypesRegistry
    if _gDefaultContentTypesRegistry is None:
        _gDefaultContentTypesRegistry = ContentTypesRegistry()
    return _gDefaultContentTypesRegistry


#---- mainline

def main():
    workspace = r"D:\master" #Local directory to define as target input.
    defines = {}
    contentTypesPaths = []
    for r,d,f in os.walk(workspace):
        for file in f:
            # Only take .c and .h as target.
            if file[-2:] in [".c", ".h"]:
                infile = os.path.join(r,file)
                # Default output directory is a folder named 'output' under the same root as the workspace folder.
                outfile = os.path.join(workspace[:workspace.rindex("\\")+1],"output",r[len(workspace)+1:],file)
                try:
                    contentTypesRegistry = ContentTypesRegistry(contentTypesPaths)
                    preprocess(workspace, infile, outfile, defines, 1,
                            contentTypesRegistry=contentTypesRegistry)
                except PreprocessError as ex:
                    if log.isDebugEnabled():
                        import traceback
                        traceback.print_exc(file=sys.stderr)
                    else:
                        sys.stderr.write("preprocess: error: %s\n" % str(ex))
                    return 1

if __name__ == "__main__":
    argv = ["preprocessor.py"]
    __file__ = argv[0]
    sys.exit( main() )
