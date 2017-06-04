package edu.mit.csail.sdg.alloy4compiler.translator;

import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;
import java.util.Stack;

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4compiler.translator.PartialInstance.Atom;
import edu.mit.csail.sdg.alloy4compiler.translator.PartialInstance.FieldRel;
import edu.mit.csail.sdg.alloy4compiler.translator.PartialInstance.Fix;
import edu.mit.csail.sdg.alloy4compiler.translator.PartialInstance.Rel;
import edu.mit.csail.sdg.alloy4compiler.translator.PartialInstance.SigRel;

public class PartialInstanceParser {

    public class PIParseException extends Err {
        private static final long serialVersionUID = -6784568945966471694L;
        public final String message;
        public final String source;
        public final int pos;
        public final Stack<String> parseStack;

        @SuppressWarnings("unchecked")
        public PIParseException(String message, String source, int pos, Stack<String> parseStack) {
            super(null, message, null);
            this.message = message;
            this.source = source;
            this.pos = pos;
            this.parseStack = (Stack<String>)parseStack.clone();
        }

        @Override
        public String getMessage() {
            String msg = message + "\nParse stack:";
            String iden = "  ";
            for (String s: parseStack) {
                msg += "\n" + iden + s;
                iden += "  ";
            }
            return msg;
        }
    }

    public static final List<Character> delims =
            Arrays.asList(',', '=', '(', ')', '<', '>', '{', '}', '[', ']', ':', ';', '.');

    private class Lexer {
        private int pos = 0;
        private String nextToken = null;
        private int nextPos = -1;

        public void skipWhitespaces() {
            while (pos < source.length() && Character.isWhitespace(source.charAt(pos))) pos++;
        }

        public String readToken() {
            if (nextToken != null) {
                pos = nextPos;
                String t = nextToken;
                nextToken = null;
                return t;
            } else {
                skipWhitespaces();
                if (pos >= source.length())      return null;
                if (isDelim(source.charAt(pos))) return "" + source.charAt(pos++);
                StringBuilder sb = new StringBuilder();
                do {
                    sb.append(source.charAt(pos++));
                } while (pos < source.length() && !isDelimOrWhitespace(source.charAt(pos)));
                return sb.toString();
            }
        }

        public String peakToken() {
            int currPos = pos;
            this.nextToken = readToken();
            this.nextPos = pos;
            this.pos = currPos;
            return nextToken;
        }

        public boolean done() {
            skipWhitespaces();
            return pos >= source.length();
        }
    }

    private String source;
    private Lexer lexer;
    private Stack<String> parseStack;

    public PartialInstanceParser(String source) {
        this.source = source == null ? "" : source;
        this.lexer = new Lexer();
        this.parseStack = new Stack<String>();
    }

    public PartialInstance parse() throws PIParseException {
        PartialInstance pi = new PartialInstance();
        while (!lexer.done()) {
            parseAssignment(pi);
        }
        return pi;
    }

    private void parseAssignment(PartialInstance pi) throws PIParseException {
        entering("Assignment");
        String iden = parseIden();
        if ("universe".equals(iden)) {
            parseDelim('=');
            pi.setUniverse(parseTuple(pi));
        } else if ("ints".equals(iden)) {
            parseDelim('=');
            pi.setInts(parseTuple(pi));
        } else if ("lowers".equals(iden) || "uppers".equals(iden) || "fix".equals(iden)) {
            parseDelim('[');
            String sigName = parseIden();
            Rel rel = null;
            if (isDelim(lexer.peakToken(), '.')) {
                parseDelim('.');
                String fldName = parseIden();
                rel = new FieldRel(sigName, fldName);
            } else {
                rel = new SigRel(sigName);
            }
            if (isDelim(lexer.peakToken(), ':')) {
                parseDelim(':');
                int idx = parseInt();
                parseDelim(':');
                String atom = parseIden();
                rel = new Fix(rel, idx, Atom.parse(atom));
            }
            parseDelim(']');
            parseDelim('=');
            if ("fix".equals(iden)) {
                pi.addFix((Fix) rel, parseTupleSet(pi));
            } else if ("lowers".equals(iden)) {
                pi.setLower(rel, parseTupleSet(pi));
            } else {
                pi.setUpper(rel, parseTupleSet(pi));
            }
        } else {
            parseFail("Error parsing 'Assignment': exected 'universe', 'lowers', or 'uppers'; got " + iden);
        }
        exiting("Assignment");
    }

    private List<Atom> parseTuple(PartialInstance pi) throws PIParseException {
        entering("Tuple");
        List<Atom> atoms = new LinkedList<Atom>();
        parseDelim('<');
        if (isIden(lexer.peakToken())) {
            atoms.add(pi.findOrNewAtom(parseIden()));
        }
        while (!isDelim(lexer.peakToken(), '>')) {
            parseDelim(',');
            atoms.add(pi.findOrNewAtom(parseIden()));
        }
        parseDelim('>');
        exiting("Tuple");
        return atoms;
    }

    private List<List<Atom>> parseTupleSet(PartialInstance pi) throws PIParseException {
        entering("TupleSet");
        List<List<Atom>> ts = new LinkedList<List<Atom>>();
        parseDelim('{');
        while (!isDelim(lexer.peakToken(), '}')) {
            ts.add(parseTuple(pi));
        }
        parseDelim('}');
        exiting("TupleSet");
        return ts;
    }

    private char parseDelim() throws PIParseException {
        entering("Delim");
        String t = lexer.readToken();
        if (!isDelim(t)) parseFail("Expected a delimiter; got " + t);
        exiting("Delim");
        return t.charAt(0);
    }

    private void parseDelim(char expected) throws PIParseException {
        entering("Delim");
        char ch = parseDelim();
        if (ch != expected) parseFail(String.format("Expected '%s'; got '%s'", expected, ch));
        exiting("Delim");
    }

    private String parseIden() throws PIParseException {
        entering("Iden");
        String iden = lexer.readToken();
        if (isDelim(iden)) parseFail("Expected identifier, got '" + iden + "'");
        exiting("Iden");
        return iden;
    }

    private int parseInt() throws PIParseException {
        String id = parseIden();
        try {
            return Integer.parseInt(id);
        } catch (NumberFormatException e) {
            parseFail("Expected int, got '" + id + "'");
            return -1; //unreachable
        }
    }

    private void entering(String ruleName) { parseStack.push(ruleName); }
    private void exiting(String ruleName)  { String r = parseStack.pop(); assert r.equals(ruleName); }

    private void parseFail(String msg) throws PIParseException {
        throw new PIParseException(msg, source, lexer.pos, parseStack);
    }

    static boolean isDelim(String str)                { return str.length() == 1 && isDelim(str.charAt(0)); }
    static boolean isDelim(char ch)                   { return delims.contains(ch); }
    static boolean isDelim(String str, char expected) { return ("" + expected).equals(str); }
    static boolean isDelimOrWhitespace(char ch)       { return isDelim(ch) || Character.isWhitespace(ch); }
    static boolean isIden(String str)                 { return !isDelim(str); }

}
