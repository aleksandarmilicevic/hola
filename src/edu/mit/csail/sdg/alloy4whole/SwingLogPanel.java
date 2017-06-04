/* Alloy Analyzer 4 -- Copyright (c) 2006-2009, Felix Chang
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files
 * (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify,
 * merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
 * LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF
 * OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

package edu.mit.csail.sdg.alloy4whole;

import java.awt.Color;
import java.awt.Dimension;
import java.awt.Font;
import java.awt.event.FocusEvent;
import java.awt.event.FocusListener;
import java.awt.event.MouseEvent;
import java.awt.event.MouseListener;
import java.util.ArrayList;
import java.util.List;
import java.util.StringTokenizer;

import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTextPane;
import javax.swing.border.EmptyBorder;
import javax.swing.text.AbstractDocument;
import javax.swing.text.BadLocationException;
import javax.swing.text.BoxView;
import javax.swing.text.Element;
import javax.swing.text.Style;
import javax.swing.text.StyleConstants;
import javax.swing.text.StyledDocument;
import javax.swing.text.StyledEditorKit;
import javax.swing.text.View;
import javax.swing.text.ViewFactory;

import edu.mit.csail.sdg.alloy4.OurAntiAlias;
import edu.mit.csail.sdg.alloy4.OurUtil;

/** This helper method is used by SimpleGUI; only the AWT Event Thread may call methods in this class. */

final class SwingLogPanel {

    public static final String[] paletteHex = new String[] {"#000000", "#2E8B57", "#FF00FF", "#696969", "#FF1493", "#A0522D", "#9932CC", "#008B8B", "#228B22", "#556B2F", "#8A2BE2", "#008080", "#C71585", "#8B4513", "#A52A2A", "#FF0000", "#008000", "#483D8B", "#2F4F4F", "#9400D3", "#006400", "#8B008B", "#8B0000", "#4B0082", "#191970", "#0000FF"};

    public static Color hex2Rgb(String colorStr) {
        return new Color(
                Integer.valueOf(colorStr.substring(1, 3), 16),
                Integer.valueOf(colorStr.substring(3, 5), 16),
                Integer.valueOf(colorStr.substring(5, 7), 16));
    }

    /** Try to wrap the input to about 60 characters per line; however, if a token is too long, we won't break it. */
    private static void linewrap(StringBuilder sb, String msg) {
        StringTokenizer tokenizer=new StringTokenizer(msg,"\r\n\t ");
        final int max=60;
        int now=0;
        while(tokenizer.hasMoreTokens()) {
            String x=tokenizer.nextToken();
            if (now+1+x.length() > max) {
                if (now>0) { sb.append('\n'); }
                sb.append(x);
                now=x.length();
            } else {
                if (now>0) { now++; sb.append(' '); }
                sb.append(x);
                now=now+x.length();
            }
        }
    }

    /** This field buffers previous calls to log() so that we can write them out later in a single Swing call
     * (If there is nothing buffered, this field can be an empty list or even null).
     */
    private final List<String> batch = new ArrayList<String>();

    /** The newly created JTextPane object that will display the log; null if this log has been destroyed. */
    private JTextPane log;

    /** The style to use when writing regular messages. */
    private final Style styleRegular;

    /** The style to use when writing bold messages. */
    private final Style styleBold;

    /** The style to use when writing red messages. */
    private final Style styleRed;

    private final Style[] palette, paletteBold;

    /** This stores the JLabels used for displaying hyperlinks. */
    private final List<JLabel> links = new ArrayList<JLabel>();

    /** When the window gains focus, we'll call handler.run(ev_logFocused);
     * When a hyperlink is clicked, we'll call handler.run(evs_visualize, linkURL).
     */
    private final SimpleGUI handler;

    /** The current length of the log, not counting any "red" error message at the end of the log. */
    private int lastSize = 0;

    /** The current font name. */
    private String fontName;

    /** The current font size. */
    private int fontSize;

    /** The color to use for hyperlinks when the mouse is not hovering over it. */
    private static final Color linkColor = new Color(0.3f, 0.3f, 0.9f);

    /** The color to use for a hyperlink when the mouse is hovering over it. */
    private static final Color hoverColor = new Color(0.9f, 0.3f, 0.3f);

    /** This stores a default ViewFactory that will handle the View requests that we don't care to override. */
    private static final ViewFactory defaultFactory = (new StyledEditorKit()).getViewFactory();

    /** Constructs a new JTextPane logger, and put it inside an existing JScrollPane.
     * @param parent - the existing JScrollPane to insert the JTextPane into
     * @param fontName - the font name to use
     * @param fontSize - the font size to use
     * @param background - the background color to use
     * @param regular - the color to use for regular messages
     * @param red - the color to use for red messages
     * @param handler - the SimpleGUI parent
     */
    public SwingLogPanel(
        final JScrollPane parent, String fontName, int fontSize,
        final Color background, final Color regular, final Color red,
        final SimpleGUI handler) {
        this.handler = handler;
        this.fontName = fontName;
        this.fontSize = fontSize;
        this.log = OurUtil.make(OurAntiAlias.pane(), Color.BLACK, background, new EmptyBorder(1,1,1,1), new Font(fontName, Font.PLAIN, fontSize));
        // This customized StyledEditorKit prevents line-wrapping up to 30000 pixels wide.
        // 30000 is a good number; value higher than about 32768 will cause errors.
        this.log.setEditorKit(new StyledEditorKit() {
            private static final long serialVersionUID = 0;
            @Override public final ViewFactory getViewFactory() {
                return new ViewFactory() {
                    public final View create(Element x) {
                        if (!AbstractDocument.SectionElementName.equals(x.getName())) return defaultFactory.create(x);
                        return new BoxView(x, View.Y_AXIS) {
                            @Override public final float getMinimumSpan(int axis) { return super.getPreferredSpan(axis); }
                            @Override public final void layout(int width,int height) { super.layout(30000, height); }
                        };
                    }
                };
            }
        });
        log.setEditable(false);
        log.addFocusListener(new FocusListener() {
            public final void focusGained(FocusEvent e) { if (handler!=null) handler.notifyFocusLost(); }
            public final void focusLost(FocusEvent e) { }
        });
        StyledDocument doc = log.getStyledDocument();
        styleRegular = doc.addStyle("regular", null);
        StyleConstants.setFontFamily(styleRegular, fontName);
        StyleConstants.setFontSize(styleRegular, fontSize);
        StyleConstants.setForeground(styleRegular, regular);
        styleBold = doc.addStyle("bold", styleRegular);
        StyleConstants.setBold(styleBold, true);
        styleRed = doc.addStyle("red", styleBold);
        StyleConstants.setForeground(styleRed, red);
        parent.setViewportView(log);
        parent.setBackground(background);
        this.palette = new Style[paletteHex.length];
        this.paletteBold = new Style[paletteHex.length];
        for (int i = 0; i < palette.length; i++) {
            Style st = doc.addStyle("palette" + i, null);
            palette[i] = st;
            StyleConstants.setFontFamily(st, fontName);
            StyleConstants.setFontSize(st, fontSize);
            StyleConstants.setForeground(st, hex2Rgb(paletteHex[i]));

            st = doc.addStyle("paletteBold" + i, null);
            paletteBold[i] = st;
            StyleConstants.setFontFamily(st, fontName);
            StyleConstants.setFontSize(st, fontSize);
            StyleConstants.setBold(st, true);
            StyleConstants.setForeground(st, hex2Rgb(paletteHex[i]));
        }
    }

    /** Write a horizontal separator into the log window. */
    public void logDivider() {
        if (log==null) return;
        clearError();
        StyledDocument doc = log.getStyledDocument();
        Style dividerStyle = doc.addStyle("bar", styleRegular);
        JPanel jpanel = new JPanel();
        jpanel.setBackground(Color.LIGHT_GRAY);
        jpanel.setPreferredSize(new Dimension(300,1)); // 300 is arbitrary, since it will auto-stretch
        StyleConstants.setComponent(dividerStyle, jpanel);
        reallyLog(".", dividerStyle); // Any character would do; "." will be replaced by the JPanel
        reallyLog("\n\n", styleRegular);
        log.setCaretPosition(doc.getLength());
        lastSize = doc.getLength();
    }

    /** Write a clickable link into the log window. */
    public void logLink(final String link, final String linkDestination)                    { logLink(null, link, linkDestination); }
    public void logLink(final Integer pos, final String link, final String linkDestination) {
        if (log==null || link.length()==0) return;
        if (linkDestination==null || linkDestination.length()==0) { flush(); logAt(pos, link); return; }
        clearError();
        StyledDocument doc = log.getStyledDocument();
        Style linkStyle = doc.addStyle("link", styleRegular);
        final JLabel label = OurUtil.make(OurAntiAlias.label(link), new Font(fontName, Font.BOLD, fontSize), linkColor);
        label.setAlignmentY(0.8f);
        label.setMaximumSize(label.getPreferredSize());
        label.addMouseListener(new MouseListener(){
            public final void mousePressed(MouseEvent e)  { if (handler!=null) handler.doVisualize(linkDestination); }
            public final void mouseClicked(MouseEvent e)  { }
            public final void mouseReleased(MouseEvent e) { }
            public final void mouseEntered(MouseEvent e)  { label.setForeground(hoverColor); }
            public final void mouseExited(MouseEvent e)   { label.setForeground(linkColor); }
        });
        StyleConstants.setComponent(linkStyle, label);
        links.add(label);
        reallyLog(pos, ".", linkStyle); // Any character would do; the "." will be replaced by the JLabel
        log.setCaretPosition(doc.getLength());
        lastSize = doc.getLength();
    }

    /** Write "msg" in regular style. */
    public void log(String msg) { if (log!=null && msg.length()>0) batch.add(msg); }

    /** Write "msg" in bold style. */
    public void logBold(String msg)            { if (msg.length()>0) {clearError(); reallyLog(msg, styleBold);} }
    public void logBoldAt(int pos, String msg) { if (msg.length()>0) {clearError(); reallyLog(pos, msg, styleBold);} }

    private void reallyLog(String text, Style style) { reallyLog(null, text, style); }
    private void reallyLog(Integer pos, String text, Style style) {
        if (log==null || text.length()==0) return;
        int i=text.lastIndexOf('\n'), j=text.lastIndexOf('\r');
        if (i>=0 && i<j) { i=j; }
        StyledDocument doc=log.getStyledDocument();
        try {
            if (i<0 || pos != null) {
                doc.insertString(pos != null ? pos : doc.getLength(), text, style);
            } else {
                // Performs intelligent caret positioning
                doc.insertString(doc.getLength(), text.substring(0,i+1), style);
                log.setCaretPosition(doc.getLength());
                if (i<text.length()-1) {
                    doc.insertString(doc.getLength(), text.substring(i+1), style);
                }
            }
        } catch (BadLocationException e) {
            // Harmless
        }
        if (style!=styleRed) { lastSize=doc.getLength(); }
    }

    public void logAt(Integer pos, String text)              { logAt(pos, text, styleRegular); }
    public void logAt(Integer pos, String text, Style style) { reallyLog(pos, text, style); }

    /** Write "msg" in red style (with automatic line wrap). */
    public void logRed (String msg) {
        if (log==null || msg==null || msg.length()==0) return;
        StringBuilder sb=new StringBuilder();
        while (msg.length()>0) {
            int i = msg.indexOf('\n');
            if (i>=0) {
                linewrap(sb, msg.substring(0,i));
                sb.append('\n');
                msg=msg.substring(i+1);
            } else {
                linewrap(sb, msg);
                break;
            }
        }
        clearError();
        reallyLog(sb.toString(), styleRed);
    }

    /** Write "msg" in regular style (with automatic line wrap). */
    public void logIndented (String msg) {
        if (log==null || msg.length()==0) return;
        StringBuilder sb=new StringBuilder();
        while(msg.length()>0) {
            int i = msg.indexOf('\n');
            if (i>=0) {
                linewrap(sb, msg.substring(0,i));
                sb.append('\n');
                msg=msg.substring(i+1);
            } else {
                linewrap(sb, msg);
                break;
            }
        }
        clearError();
        reallyLog(sb.toString(), styleRegular);
    }

    /** Set the font name. */
    public void setFontName(String fontName) {
        if (log==null) return;
        this.fontName = fontName;
        log.setFont(new Font(fontName, Font.PLAIN, fontSize));
        StyleConstants.setFontFamily(styleRegular, fontName);
        StyleConstants.setFontFamily(styleBold, fontName);
        StyleConstants.setFontFamily(styleRed, fontName);
        StyleConstants.setFontSize(styleRegular, fontSize);
        StyleConstants.setFontSize(styleBold, fontSize);
        StyleConstants.setFontSize(styleRed, fontSize);
        // Changes all existing text
        StyledDocument doc=log.getStyledDocument();
        Style temp=doc.addStyle("temp", null);
        StyleConstants.setFontFamily(temp, fontName);
        StyleConstants.setFontSize(temp, fontSize);
        doc.setCharacterAttributes(0, doc.getLength(), temp, false);
        // Changes all existing hyperlinks
        Font newFont = new Font(fontName, Font.BOLD, fontSize);
        for(JLabel link: links) { link.setFont(newFont); }
    }

    /** Set the font size. */
    public void setFontSize(int fontSize) {
        if (log==null) return;
        this.fontSize = fontSize;
        setFontName(this.fontName);
    }

    /** Set the background color. */
    public void setBackground(Color background) {
        if (log==null) return;
        log.setBackground(background);
    }

    /** Query the current length of the log. */
    int getLength() {
        if (log==null) return 0;
        clearError();
        return log.getStyledDocument().getLength();
    }

    /** Truncate the log to the given length; if the log is shorter than the number given, then nothing happens. */
    void setLength(int newLength) {
        if (log==null) return;
        clearError();
        StyledDocument doc=log.getStyledDocument();
        int n=doc.getLength();
        if (n<=newLength) return;
        try {
            doc.remove(newLength, n-newLength);
        } catch (BadLocationException e) {
            // Harmless
        }
        if (lastSize>doc.getLength()) { lastSize=doc.getLength(); }
    }

    /** This method copies the currently selected text in the log (if any) into the clipboard. */
    public void copy() {
        if (log==null) return;
        log.copy();
    }

    /** Removes any messages writtin in "red" style. */
    public void clearError() {
        if (log==null) return;
        // Since this class always removes "red" messages prior to writing anything,
        // that means if there are any red messages, they will always be at the end of the JTextPane.
        StyledDocument doc=log.getStyledDocument();
        int n=doc.getLength();
        if (n>lastSize) {
            try {doc.remove(lastSize, n-lastSize);} catch (BadLocationException e) {}
        }
        if (batch.size()>0) {
            for(String msg: batch) { reallyLog(msg, styleRegular); }
            batch.clear();
        }
    }

    /** Commits all outstanding writes (if the messages are buffered). */
    public void flush() {
        if (log==null) return;
        if (batch.size()>0) clearError();
    }

    public void logPaletteBold(String text, int paletteIdx)                 { logPalette(paletteBold, text, paletteIdx); }
    public void logPalette(String text, int paletteIdx)                     { logPalette(palette, text, paletteIdx); }
    private void logPalette(Style[] palette, String text, int paletteIdx) {
        flush();
        reallyLog(text, palette[paletteIdx % palette.length]);
    }
}
