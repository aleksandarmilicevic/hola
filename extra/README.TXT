The Alloy Analyzer

    The Alloy Analyzer is a tool developed by the Software Design
    Group (http://sdg.csail.mit.edu/) for analyzing models written in
    Alloy, a simple structural modeling language based on first-order
    logic. The tool can generate instances of invariants, simulate
    the execution of operations (even those defined implicitly), and
    check user-specified properties of a model. Alloy and its
    analyzer have been used primarily to explore abstract software
    designs. Its use in analyzing code for conformance to a
    specification and as an automatic test case generator are being
    investigated in ongoing research projects.

    See the web page for a description of what's new in Alloy:

        http://alloy.mit.edu/


Detailed Instructions:

    1.  Java 5 or later

        Java runtimes are available at no economic charge from Sun and
        IBM and others.  One may have come pre-installed in your OS.
        Alloy does not currently work with gcj because of its limited
        library support.

    2.  Running Alloy on Mac OS X

        Just double-click on the dmg file,
        then drag the Alloy application into your application directory.

    3.  Running Alloy on other platforms

        Just double-click on the jar file, or type:

            java -jar alloy4.jar

The source code for the Alloy Analyzer is available
under the MIT license.

The Alloy Analyzer utilizes several third-party packages whose code may
be distributed under a different license (see the various LICENSE files
in the distribution for details). We are extremely grateful to the authors
of these packages for making their source code freely available.

    * Kodkod
      http://web.mit.edu/~emina/www/kodkod.html

    * CUP Parser Generator for Java
      http://www2.cs.tum.edu/projects/cup/

    * JFlex scanner generator for Java
      http://jflex.de/

    * The zChaff solver
      http://www.princeton.edu/~chaff/zchaff.html

    * The MiniSat solver
      http://www.cs.chalmers.se/Cs/Research/FormalMethods/MiniSat/

    * The SAT4J solver
      http://www.sat4j.org/
