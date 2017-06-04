package edu.mit.csail.sdg.alloy4compiler.translator;

import static org.junit.Assert.assertArrayEquals;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

import java.util.Arrays;
import java.util.List;

import kodkod.ast.Relation;

import org.junit.After;
import org.junit.AfterClass;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4compiler.ast.Command;
import edu.mit.csail.sdg.alloy4compiler.ast.Module;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig.Field;
import edu.mit.csail.sdg.alloy4compiler.parser.CompUtil;
import edu.mit.csail.sdg.alloy4compiler.translator.PartialInstance.Atom;
import edu.mit.csail.sdg.alloy4compiler.translator.PartialInstanceParser.PIParseException;

public class PartialInstanceParserTest {

    static String model, partialInstance;

    @BeforeClass
    public static void setUpBeforeClass() throws Exception {
        model = "module SudokuModel \n" +
        		"sig Sudoku  {\n" +
        		"  grid: Int ->  Int -> lone Int \n" +
        		"} { \n" +
        		"  (this.@grid[Int]).Int in 0 + 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 \n" +
        		"  this.@grid.Int.Int in 0 + 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 \n" +
        		"}  " +
        		"pred solved[s: Sudoku] { \n" +
        		"  all r: 0 + 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 { \n" +
        		"    s.grid[r][Int] = 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 \n" +
        		"    s.grid[Int][r] = 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 \n" +
        		"  }\n" +
        		"  s.grid[(0 + 1 + 2)][(0 + 1 + 2)] = 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9\n" +
        		"  s.grid[(0 + 1 + 2)][(3 + 4 + 5)] = 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9\n" +
        		"  s.grid[(0 + 1 + 2)][(6 + 7 + 8)] = 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9\n" +
        		"  s.grid[(3 + 4 + 5)][(0 + 1 + 2)] = 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9\n" +
        		"  s.grid[(3 + 4 + 5)][(3 + 4 + 5)] = 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9\n" +
        		"  s.grid[(3 + 4 + 5)][(6 + 7 + 8)] = 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9\n" +
        		"  s.grid[(6 + 7 + 8)][(0 + 1 + 2)] = 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9\n" +
        		"  s.grid[(6 + 7 + 8)][(3 + 4 + 5)] = 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9\n" +
        		"  s.grid[(6 + 7 + 8)][(6 + 7 + 8)] = 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9\n" +
        		"}\n" +
        		"run solved for 3 but 5 Int";
        partialInstance =
                "universe = <Sudoku$0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9>" +
        		"lowers[Sudoku.grid] =  {<Sudoku$0, 0, 6, 9><Sudoku$0, 0, 7, 5><Sudoku$0, 1, 1, 8><Sudoku$0, 1, 3, 7><Sudoku$0, 1, 6, 6><Sudoku$0, 2, 0, 4><Sudoku$0, 2, 4, 6><Sudoku$0, 2, 5, 8><Sudoku$0, 3, 0, 3><Sudoku$0, 3, 4, 5><Sudoku$0, 3, 6, 7><Sudoku$0, 3, 8, 2><Sudoku$0, 4, 3, 9><Sudoku$0, 4, 5, 4><Sudoku$0, 5, 0, 2><Sudoku$0, 5, 2, 6><Sudoku$0, 5, 4, 1><Sudoku$0, 5, 8, 5><Sudoku$0, 6, 3, 1><Sudoku$0, 6, 4, 8><Sudoku$0, 6, 8, 9><Sudoku$0, 7, 2, 2><Sudoku$0, 7, 5, 3><Sudoku$0, 7, 7, 6><Sudoku$0, 8, 1, 3><Sudoku$0, 8, 2, 5>}" +
        		"lowers[Sudoku] = {<Sudoku$0>}" +
        		"uppers[Sudoku.grid] = {<Sudoku$0, 0, 6, 9><Sudoku$0, 0, 7, 5><Sudoku$0, 1, 1, 8><Sudoku$0, 1, 3, 7><Sudoku$0, 1, 6, 6><Sudoku$0, 2, 0, 4><Sudoku$0, 2, 4, 6><Sudoku$0, 2, 5, 8><Sudoku$0, 3, 0, 3><Sudoku$0, 3, 4, 5><Sudoku$0, 3, 6, 7><Sudoku$0, 3, 8, 2><Sudoku$0, 4, 3, 9><Sudoku$0, 4, 5, 4><Sudoku$0, 5, 0, 2><Sudoku$0, 5, 2, 6><Sudoku$0, 5, 4, 1><Sudoku$0, 5, 8, 5><Sudoku$0, 6, 3, 1><Sudoku$0, 6, 4, 8><Sudoku$0, 6, 8, 9><Sudoku$0, 7, 2, 2><Sudoku$0, 7, 5, 3><Sudoku$0, 7, 7, 6><Sudoku$0, 8, 1, 3><Sudoku$0, 8, 2, 5><Sudoku$0, 0, 0, 1><Sudoku$0, 0, 0, 2><Sudoku$0, 0, 0, 3><Sudoku$0, 0, 0, 4><Sudoku$0, 0, 0, 5><Sudoku$0, 0, 0, 6><Sudoku$0, 0, 0, 7><Sudoku$0, 0, 0, 8><Sudoku$0, 0, 0, 9><Sudoku$0, 0, 1, 1><Sudoku$0, 0, 1, 2><Sudoku$0, 0, 1, 3><Sudoku$0, 0, 1, 4><Sudoku$0, 0, 1, 5><Sudoku$0, 0, 1, 6><Sudoku$0, 0, 1, 7><Sudoku$0, 0, 1, 8><Sudoku$0, 0, 1, 9><Sudoku$0, 0, 2, 1><Sudoku$0, 0, 2, 2><Sudoku$0, 0, 2, 3><Sudoku$0, 0, 2, 4><Sudoku$0, 0, 2, 5><Sudoku$0, 0, 2, 6><Sudoku$0, 0, 2, 7><Sudoku$0, 0, 2, 8><Sudoku$0, 0, 2, 9><Sudoku$0, 0, 3, 1><Sudoku$0, 0, 3, 2><Sudoku$0, 0, 3, 3><Sudoku$0, 0, 3, 4><Sudoku$0, 0, 3, 5><Sudoku$0, 0, 3, 6><Sudoku$0, 0, 3, 7><Sudoku$0, 0, 3, 8><Sudoku$0, 0, 3, 9><Sudoku$0, 0, 4, 1><Sudoku$0, 0, 4, 2><Sudoku$0, 0, 4, 3><Sudoku$0, 0, 4, 4><Sudoku$0, 0, 4, 5><Sudoku$0, 0, 4, 6><Sudoku$0, 0, 4, 7><Sudoku$0, 0, 4, 8><Sudoku$0, 0, 4, 9><Sudoku$0, 0, 5, 1><Sudoku$0, 0, 5, 2><Sudoku$0, 0, 5, 3><Sudoku$0, 0, 5, 4><Sudoku$0, 0, 5, 5><Sudoku$0, 0, 5, 6><Sudoku$0, 0, 5, 7><Sudoku$0, 0, 5, 8><Sudoku$0, 0, 5, 9><Sudoku$0, 0, 8, 1><Sudoku$0, 0, 8, 2><Sudoku$0, 0, 8, 3><Sudoku$0, 0, 8, 4><Sudoku$0, 0, 8, 5><Sudoku$0, 0, 8, 6><Sudoku$0, 0, 8, 7><Sudoku$0, 0, 8, 8><Sudoku$0, 0, 8, 9><Sudoku$0, 1, 0, 1><Sudoku$0, 1, 0, 2><Sudoku$0, 1, 0, 3><Sudoku$0, 1, 0, 4><Sudoku$0, 1, 0, 5><Sudoku$0, 1, 0, 6><Sudoku$0, 1, 0, 7><Sudoku$0, 1, 0, 8><Sudoku$0, 1, 0, 9><Sudoku$0, 1, 2, 1><Sudoku$0, 1, 2, 2><Sudoku$0, 1, 2, 3><Sudoku$0, 1, 2, 4><Sudoku$0, 1, 2, 5><Sudoku$0, 1, 2, 6><Sudoku$0, 1, 2, 7><Sudoku$0, 1, 2, 8><Sudoku$0, 1, 2, 9><Sudoku$0, 1, 4, 1><Sudoku$0, 1, 4, 2><Sudoku$0, 1, 4, 3><Sudoku$0, 1, 4, 4><Sudoku$0, 1, 4, 5><Sudoku$0, 1, 4, 6><Sudoku$0, 1, 4, 7><Sudoku$0, 1, 4, 8><Sudoku$0, 1, 4, 9><Sudoku$0, 1, 5, 1><Sudoku$0, 1, 5, 2><Sudoku$0, 1, 5, 3><Sudoku$0, 1, 5, 4><Sudoku$0, 1, 5, 5><Sudoku$0, 1, 5, 6><Sudoku$0, 1, 5, 7><Sudoku$0, 1, 5, 8><Sudoku$0, 1, 5, 9><Sudoku$0, 1, 7, 1><Sudoku$0, 1, 7, 2><Sudoku$0, 1, 7, 3><Sudoku$0, 1, 7, 4><Sudoku$0, 1, 7, 5><Sudoku$0, 1, 7, 6><Sudoku$0, 1, 7, 7><Sudoku$0, 1, 7, 8><Sudoku$0, 1, 7, 9><Sudoku$0, 1, 8, 1><Sudoku$0, 1, 8, 2><Sudoku$0, 1, 8, 3><Sudoku$0, 1, 8, 4><Sudoku$0, 1, 8, 5><Sudoku$0, 1, 8, 6><Sudoku$0, 1, 8, 7><Sudoku$0, 1, 8, 8><Sudoku$0, 1, 8, 9><Sudoku$0, 2, 1, 1><Sudoku$0, 2, 1, 2><Sudoku$0, 2, 1, 3><Sudoku$0, 2, 1, 4><Sudoku$0, 2, 1, 5><Sudoku$0, 2, 1, 6><Sudoku$0, 2, 1, 7><Sudoku$0, 2, 1, 8><Sudoku$0, 2, 1, 9><Sudoku$0, 2, 2, 1><Sudoku$0, 2, 2, 2><Sudoku$0, 2, 2, 3><Sudoku$0, 2, 2, 4><Sudoku$0, 2, 2, 5><Sudoku$0, 2, 2, 6><Sudoku$0, 2, 2, 7><Sudoku$0, 2, 2, 8><Sudoku$0, 2, 2, 9><Sudoku$0, 2, 3, 1><Sudoku$0, 2, 3, 2><Sudoku$0, 2, 3, 3><Sudoku$0, 2, 3, 4><Sudoku$0, 2, 3, 5><Sudoku$0, 2, 3, 6><Sudoku$0, 2, 3, 7><Sudoku$0, 2, 3, 8><Sudoku$0, 2, 3, 9><Sudoku$0, 2, 6, 1><Sudoku$0, 2, 6, 2><Sudoku$0, 2, 6, 3><Sudoku$0, 2, 6, 4><Sudoku$0, 2, 6, 5><Sudoku$0, 2, 6, 6><Sudoku$0, 2, 6, 7><Sudoku$0, 2, 6, 8><Sudoku$0, 2, 6, 9><Sudoku$0, 2, 7, 1><Sudoku$0, 2, 7, 2><Sudoku$0, 2, 7, 3><Sudoku$0, 2, 7, 4><Sudoku$0, 2, 7, 5><Sudoku$0, 2, 7, 6><Sudoku$0, 2, 7, 7><Sudoku$0, 2, 7, 8><Sudoku$0, 2, 7, 9><Sudoku$0, 2, 8, 1><Sudoku$0, 2, 8, 2><Sudoku$0, 2, 8, 3><Sudoku$0, 2, 8, 4><Sudoku$0, 2, 8, 5><Sudoku$0, 2, 8, 6><Sudoku$0, 2, 8, 7><Sudoku$0, 2, 8, 8><Sudoku$0, 2, 8, 9><Sudoku$0, 3, 1, 1><Sudoku$0, 3, 1, 2><Sudoku$0, 3, 1, 3><Sudoku$0, 3, 1, 4><Sudoku$0, 3, 1, 5><Sudoku$0, 3, 1, 6><Sudoku$0, 3, 1, 7><Sudoku$0, 3, 1, 8><Sudoku$0, 3, 1, 9><Sudoku$0, 3, 2, 1><Sudoku$0, 3, 2, 2><Sudoku$0, 3, 2, 3><Sudoku$0, 3, 2, 4><Sudoku$0, 3, 2, 5><Sudoku$0, 3, 2, 6><Sudoku$0, 3, 2, 7><Sudoku$0, 3, 2, 8><Sudoku$0, 3, 2, 9><Sudoku$0, 3, 3, 1><Sudoku$0, 3, 3, 2><Sudoku$0, 3, 3, 3><Sudoku$0, 3, 3, 4><Sudoku$0, 3, 3, 5><Sudoku$0, 3, 3, 6><Sudoku$0, 3, 3, 7><Sudoku$0, 3, 3, 8><Sudoku$0, 3, 3, 9><Sudoku$0, 3, 5, 1><Sudoku$0, 3, 5, 2><Sudoku$0, 3, 5, 3><Sudoku$0, 3, 5, 4><Sudoku$0, 3, 5, 5><Sudoku$0, 3, 5, 6><Sudoku$0, 3, 5, 7><Sudoku$0, 3, 5, 8><Sudoku$0, 3, 5, 9><Sudoku$0, 3, 7, 1><Sudoku$0, 3, 7, 2><Sudoku$0, 3, 7, 3><Sudoku$0, 3, 7, 4><Sudoku$0, 3, 7, 5><Sudoku$0, 3, 7, 6><Sudoku$0, 3, 7, 7><Sudoku$0, 3, 7, 8><Sudoku$0, 3, 7, 9><Sudoku$0, 4, 0, 1><Sudoku$0, 4, 0, 2><Sudoku$0, 4, 0, 3><Sudoku$0, 4, 0, 4><Sudoku$0, 4, 0, 5><Sudoku$0, 4, 0, 6><Sudoku$0, 4, 0, 7><Sudoku$0, 4, 0, 8><Sudoku$0, 4, 0, 9><Sudoku$0, 4, 1, 1><Sudoku$0, 4, 1, 2><Sudoku$0, 4, 1, 3><Sudoku$0, 4, 1, 4><Sudoku$0, 4, 1, 5><Sudoku$0, 4, 1, 6><Sudoku$0, 4, 1, 7><Sudoku$0, 4, 1, 8><Sudoku$0, 4, 1, 9><Sudoku$0, 4, 2, 1><Sudoku$0, 4, 2, 2><Sudoku$0, 4, 2, 3><Sudoku$0, 4, 2, 4><Sudoku$0, 4, 2, 5><Sudoku$0, 4, 2, 6><Sudoku$0, 4, 2, 7><Sudoku$0, 4, 2, 8><Sudoku$0, 4, 2, 9><Sudoku$0, 4, 4, 1><Sudoku$0, 4, 4, 2><Sudoku$0, 4, 4, 3><Sudoku$0, 4, 4, 4><Sudoku$0, 4, 4, 5><Sudoku$0, 4, 4, 6><Sudoku$0, 4, 4, 7><Sudoku$0, 4, 4, 8><Sudoku$0, 4, 4, 9><Sudoku$0, 4, 6, 1><Sudoku$0, 4, 6, 2><Sudoku$0, 4, 6, 3><Sudoku$0, 4, 6, 4><Sudoku$0, 4, 6, 5><Sudoku$0, 4, 6, 6><Sudoku$0, 4, 6, 7><Sudoku$0, 4, 6, 8><Sudoku$0, 4, 6, 9><Sudoku$0, 4, 7, 1><Sudoku$0, 4, 7, 2><Sudoku$0, 4, 7, 3><Sudoku$0, 4, 7, 4><Sudoku$0, 4, 7, 5><Sudoku$0, 4, 7, 6><Sudoku$0, 4, 7, 7><Sudoku$0, 4, 7, 8><Sudoku$0, 4, 7, 9><Sudoku$0, 4, 8, 1><Sudoku$0, 4, 8, 2><Sudoku$0, 4, 8, 3><Sudoku$0, 4, 8, 4><Sudoku$0, 4, 8, 5><Sudoku$0, 4, 8, 6><Sudoku$0, 4, 8, 7><Sudoku$0, 4, 8, 8><Sudoku$0, 4, 8, 9><Sudoku$0, 5, 1, 1><Sudoku$0, 5, 1, 2><Sudoku$0, 5, 1, 3><Sudoku$0, 5, 1, 4><Sudoku$0, 5, 1, 5><Sudoku$0, 5, 1, 6><Sudoku$0, 5, 1, 7><Sudoku$0, 5, 1, 8><Sudoku$0, 5, 1, 9><Sudoku$0, 5, 3, 1><Sudoku$0, 5, 3, 2><Sudoku$0, 5, 3, 3><Sudoku$0, 5, 3, 4><Sudoku$0, 5, 3, 5><Sudoku$0, 5, 3, 6><Sudoku$0, 5, 3, 7><Sudoku$0, 5, 3, 8><Sudoku$0, 5, 3, 9><Sudoku$0, 5, 5, 1><Sudoku$0, 5, 5, 2><Sudoku$0, 5, 5, 3><Sudoku$0, 5, 5, 4><Sudoku$0, 5, 5, 5><Sudoku$0, 5, 5, 6><Sudoku$0, 5, 5, 7><Sudoku$0, 5, 5, 8><Sudoku$0, 5, 5, 9><Sudoku$0, 5, 6, 1><Sudoku$0, 5, 6, 2><Sudoku$0, 5, 6, 3><Sudoku$0, 5, 6, 4><Sudoku$0, 5, 6, 5><Sudoku$0, 5, 6, 6><Sudoku$0, 5, 6, 7><Sudoku$0, 5, 6, 8><Sudoku$0, 5, 6, 9><Sudoku$0, 5, 7, 1><Sudoku$0, 5, 7, 2><Sudoku$0, 5, 7, 3><Sudoku$0, 5, 7, 4><Sudoku$0, 5, 7, 5><Sudoku$0, 5, 7, 6><Sudoku$0, 5, 7, 7><Sudoku$0, 5, 7, 8><Sudoku$0, 5, 7, 9><Sudoku$0, 6, 0, 1><Sudoku$0, 6, 0, 2><Sudoku$0, 6, 0, 3><Sudoku$0, 6, 0, 4><Sudoku$0, 6, 0, 5><Sudoku$0, 6, 0, 6><Sudoku$0, 6, 0, 7><Sudoku$0, 6, 0, 8><Sudoku$0, 6, 0, 9><Sudoku$0, 6, 1, 1><Sudoku$0, 6, 1, 2><Sudoku$0, 6, 1, 3><Sudoku$0, 6, 1, 4><Sudoku$0, 6, 1, 5><Sudoku$0, 6, 1, 6><Sudoku$0, 6, 1, 7><Sudoku$0, 6, 1, 8><Sudoku$0, 6, 1, 9><Sudoku$0, 6, 2, 1><Sudoku$0, 6, 2, 2><Sudoku$0, 6, 2, 3><Sudoku$0, 6, 2, 4><Sudoku$0, 6, 2, 5><Sudoku$0, 6, 2, 6><Sudoku$0, 6, 2, 7><Sudoku$0, 6, 2, 8><Sudoku$0, 6, 2, 9><Sudoku$0, 6, 5, 1><Sudoku$0, 6, 5, 2><Sudoku$0, 6, 5, 3><Sudoku$0, 6, 5, 4><Sudoku$0, 6, 5, 5><Sudoku$0, 6, 5, 6><Sudoku$0, 6, 5, 7><Sudoku$0, 6, 5, 8><Sudoku$0, 6, 5, 9><Sudoku$0, 6, 6, 1><Sudoku$0, 6, 6, 2><Sudoku$0, 6, 6, 3><Sudoku$0, 6, 6, 4><Sudoku$0, 6, 6, 5><Sudoku$0, 6, 6, 6><Sudoku$0, 6, 6, 7><Sudoku$0, 6, 6, 8><Sudoku$0, 6, 6, 9><Sudoku$0, 6, 7, 1><Sudoku$0, 6, 7, 2><Sudoku$0, 6, 7, 3><Sudoku$0, 6, 7, 4><Sudoku$0, 6, 7, 5><Sudoku$0, 6, 7, 6><Sudoku$0, 6, 7, 7><Sudoku$0, 6, 7, 8><Sudoku$0, 6, 7, 9><Sudoku$0, 7, 0, 1><Sudoku$0, 7, 0, 2><Sudoku$0, 7, 0, 3><Sudoku$0, 7, 0, 4><Sudoku$0, 7, 0, 5><Sudoku$0, 7, 0, 6><Sudoku$0, 7, 0, 7><Sudoku$0, 7, 0, 8><Sudoku$0, 7, 0, 9><Sudoku$0, 7, 1, 1><Sudoku$0, 7, 1, 2><Sudoku$0, 7, 1, 3><Sudoku$0, 7, 1, 4><Sudoku$0, 7, 1, 5><Sudoku$0, 7, 1, 6><Sudoku$0, 7, 1, 7><Sudoku$0, 7, 1, 8><Sudoku$0, 7, 1, 9><Sudoku$0, 7, 3, 1><Sudoku$0, 7, 3, 2><Sudoku$0, 7, 3, 3><Sudoku$0, 7, 3, 4><Sudoku$0, 7, 3, 5><Sudoku$0, 7, 3, 6><Sudoku$0, 7, 3, 7><Sudoku$0, 7, 3, 8><Sudoku$0, 7, 3, 9><Sudoku$0, 7, 4, 1><Sudoku$0, 7, 4, 2><Sudoku$0, 7, 4, 3><Sudoku$0, 7, 4, 4><Sudoku$0, 7, 4, 5><Sudoku$0, 7, 4, 6><Sudoku$0, 7, 4, 7><Sudoku$0, 7, 4, 8><Sudoku$0, 7, 4, 9><Sudoku$0, 7, 6, 1><Sudoku$0, 7, 6, 2><Sudoku$0, 7, 6, 3><Sudoku$0, 7, 6, 4><Sudoku$0, 7, 6, 5><Sudoku$0, 7, 6, 6><Sudoku$0, 7, 6, 7><Sudoku$0, 7, 6, 8><Sudoku$0, 7, 6, 9><Sudoku$0, 7, 8, 1><Sudoku$0, 7, 8, 2><Sudoku$0, 7, 8, 3><Sudoku$0, 7, 8, 4><Sudoku$0, 7, 8, 5><Sudoku$0, 7, 8, 6><Sudoku$0, 7, 8, 7><Sudoku$0, 7, 8, 8><Sudoku$0, 7, 8, 9><Sudoku$0, 8, 0, 1><Sudoku$0, 8, 0, 2><Sudoku$0, 8, 0, 3><Sudoku$0, 8, 0, 4><Sudoku$0, 8, 0, 5><Sudoku$0, 8, 0, 6><Sudoku$0, 8, 0, 7><Sudoku$0, 8, 0, 8><Sudoku$0, 8, 0, 9><Sudoku$0, 8, 3, 1><Sudoku$0, 8, 3, 2><Sudoku$0, 8, 3, 3><Sudoku$0, 8, 3, 4><Sudoku$0, 8, 3, 5><Sudoku$0, 8, 3, 6><Sudoku$0, 8, 3, 7><Sudoku$0, 8, 3, 8><Sudoku$0, 8, 3, 9><Sudoku$0, 8, 4, 1><Sudoku$0, 8, 4, 2><Sudoku$0, 8, 4, 3><Sudoku$0, 8, 4, 4><Sudoku$0, 8, 4, 5><Sudoku$0, 8, 4, 6><Sudoku$0, 8, 4, 7><Sudoku$0, 8, 4, 8><Sudoku$0, 8, 4, 9><Sudoku$0, 8, 5, 1><Sudoku$0, 8, 5, 2><Sudoku$0, 8, 5, 3><Sudoku$0, 8, 5, 4><Sudoku$0, 8, 5, 5><Sudoku$0, 8, 5, 6><Sudoku$0, 8, 5, 7><Sudoku$0, 8, 5, 8><Sudoku$0, 8, 5, 9><Sudoku$0, 8, 6, 1><Sudoku$0, 8, 6, 2><Sudoku$0, 8, 6, 3><Sudoku$0, 8, 6, 4><Sudoku$0, 8, 6, 5><Sudoku$0, 8, 6, 6><Sudoku$0, 8, 6, 7><Sudoku$0, 8, 6, 8><Sudoku$0, 8, 6, 9><Sudoku$0, 8, 7, 1><Sudoku$0, 8, 7, 2><Sudoku$0, 8, 7, 3><Sudoku$0, 8, 7, 4><Sudoku$0, 8, 7, 5><Sudoku$0, 8, 7, 6><Sudoku$0, 8, 7, 7><Sudoku$0, 8, 7, 8><Sudoku$0, 8, 7, 9><Sudoku$0, 8, 8, 1><Sudoku$0, 8, 8, 2><Sudoku$0, 8, 8, 3><Sudoku$0, 8, 8, 4><Sudoku$0, 8, 8, 5><Sudoku$0, 8, 8, 6><Sudoku$0, 8, 8, 7><Sudoku$0, 8, 8, 8><Sudoku$0, 8, 8, 9>}" +
                "uppers[Sudoku] = {<Sudoku$0>}\n" +
                "ints = <0, 1, 2, 3, 4, 5, 6, 7, 8, 9>";
    }

    @AfterClass
    public static void tearDownAfterClass() throws Exception {
    }

    @Before
    public void setUp() throws Exception {
    }

    @After
    public void tearDown() throws Exception {
    }

    @Test
    public void testParse() throws PIParseException {
        PartialInstanceParser pip = new PartialInstanceParser(partialInstance);
        PartialInstance pi = pip.parse();
        assertNotNull(pi);
        assertEquals(11, pi.getUniverse().size());
        int[] ints = pi.ints();
        Arrays.sort(ints);
        assertArrayEquals(new int[] {0,1,2,3,4,5,6,7,8,9}, ints);
        {
            List<Atom> tsl = pi.sigLower("Sudoku");
            assertEquals(1, tsl.size());

            List<Atom> tsu = pi.sigUpper("Sudoku");
            assertEquals(1, tsu.size());
            assertTrue(tsu.get(0) == tsl.get(0));
        }
        {
            List<List<Atom>> tsl = pi.fldLower("Sudoku", "grid");
            assertEquals(26, tsl.size());
            assertEquals(4, tsl.get(0).size());

            List<List<Atom>> tsu = pi.fldUpper("Sudoku", "grid");
            assertEquals(521, tsu.size());
            assertEquals(4, tsu.get(0).size());
            assertTrue(tsu.get(0).get(0) == tsl.get(0).get(0));
        }
    }

    @Test
    public void testSolve() throws PIParseException, Err {
        A4Reporter rep = new A4Reporter();
        Module world = CompUtil.parseEverything_fromString(rep, model);
        A4Options opt = new A4Options();
        opt.partialInstance = partialInstance;
        opt.solver = A4Options.SatSolver.SAT4J;
        Command cmd = world.getAllCommands().get(0);
        A4Solution sol = TranslateAlloyToKodkod.execute_commandFromBook(rep, world.getAllReachableSigs(), cmd, opt);
        assertTrue(sol.satisfiable());

        Sig sudokuSig = world.getAllSigs().get(0);
        Field gridFld = sudokuSig.getFields().get(0);
        assertEquals(26, sol.getBounds().lowerBound((Relation) sol.a2k(gridFld)).size());
        assertEquals(521, sol.getBounds().upperBound((Relation) sol.a2k(gridFld)).size());

        assertEquals(1, sol.getBounds().lowerBound((Relation) sol.a2k(sudokuSig)).size());
        assertEquals(1, sol.getBounds().upperBound((Relation) sol.a2k(sudokuSig)).size());

        System.out.println(sol.getBounds());
        System.out.println();
        System.out.println(sol);
    }

}
