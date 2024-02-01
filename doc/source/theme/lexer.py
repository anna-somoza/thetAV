import re

from pygments.lexers.python import *

line_re = re.compile('.*?\n')

from pygments.lexer import do_insertions
from pygments.token import Name, Generic


def setup(app):
    app.add_lexer('sagecon', SageConsoleLexer)


class SageConsoleLexer(PythonConsoleLexer):

    def get_tokens_unprocessed(self, text):
        if self.python3:
            try:
                pylexer = Python3Lexer(**self.options)
                tblexer = Python3TracebackLexer(**self.options)
            except NameError:
                pylexer = PythonLexer(**self.options)
                tblexer = PythonTracebackLexer(**self.options)
        else:
            try:
                pylexer = Python2Lexer(**self.options)
                tblexer = Python2TracebackLexer(**self.options)
            except NameError:
                pylexer = PythonLexer(**self.options)
                tblexer = PythonTracebackLexer(**self.options)

        curcode = ''
        insertions = []
        curtb = ''
        tbindex = 0
        tb = 0
        for match in line_re.finditer(text):
            line = match.group()
            if line.startswith('sage: ') or line.startswith('....: '):
                tb = 0
                insertions.append((len(curcode),
                                   [(0, Generic.Prompt, line[:6])]))
                curcode += line[6:]
            elif line.rstrip() == '...' and not tb:
                # only a new >>> prompt can end an exception block
                # otherwise an ellipsis in place of the traceback frames
                # will be mishandled
                insertions.append((len(curcode),
                                   [(0, Generic.Prompt, '...')]))
                curcode += line[3:]
            else:
                if curcode:
                    for item in do_insertions(
                            insertions, pylexer.get_tokens_unprocessed(curcode)):
                        yield item
                    curcode = ''
                    insertions = []
                if (line.startswith('Traceback (most recent call last):') or
                        re.match(' {2}File "[^"]+", line \d+\n$', line)):
                    tb = 1
                    curtb = line
                    tbindex = match.start()
                elif line == 'KeyboardInterrupt\n':
                    yield match.start(), Name.Class, line
                elif tb:
                    curtb += line
                    if not (line.startswith(' ') or line.strip() == '...'):
                        tb = 0
                        for i, t, v in tblexer.get_tokens_unprocessed(curtb):
                            yield tbindex+i, t, v
                        curtb = ''
                else:
                    yield match.start(), Generic.Output, line
        if curcode:
            for item in do_insertions(insertions,
                                      pylexer.get_tokens_unprocessed(curcode)):
                yield item
        if curtb:
            for i, t, v in tblexer.get_tokens_unprocessed(curtb):
                yield tbindex+i, t, v
