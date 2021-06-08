/* Generated By:JavaCC: Do not edit this line. MappingParser.java */
package fr.univlyon1.mif37.dex.parser;

import fr.univlyon1.mif37.dex.mapping.*;
import java.util.*;


public class MappingParser implements MappingParserConstants {

/** Rules */
  final public Mapping mapping() throws ParseException {
    Collection<Relation> sourceRelations;
    Collection<AbstractRelation> targetRelations;
    Collection<Tgd> tgds;
    jj_consume_token(EDB);
    sourceRelations = tables();
    jj_consume_token(IDB);
    targetRelations = tablesIDB();
    jj_consume_token(MAPPING);
    tgds = tgds();
      {if (true) return new Mapping(sourceRelations,targetRelations,tgds);}
    throw new Error("Missing return statement in function");
  }

  final public Collection<Relation> tables() throws ParseException {
    Token t;
    Collection<Relation> result = new ArrayList<Relation>();
    List<String> args;
    String name;
    label_1:
    while (true) {
      t = jj_consume_token(IDENTIFIER);
      jj_consume_token(15);
            name = t.image;
            args = new ArrayList<String>();
      t = jj_consume_token(IDENTIFIER);
                               args.add(t.image);
      label_2:
      while (true) {
        switch ((jj_ntk==-1)?jj_ntk():jj_ntk) {
        case 16:
          ;
          break;
        default:
          jj_la1[0] = jj_gen;
          break label_2;
        }
        jj_consume_token(16);
        t = jj_consume_token(IDENTIFIER);
                                    args.add(t.image);
      }
      jj_consume_token(17);
              result.add(new Relation(name,args));
      switch ((jj_ntk==-1)?jj_ntk():jj_ntk) {
      case IDENTIFIER:
        ;
        break;
      default:
        jj_la1[1] = jj_gen;
        break label_1;
      }
    }
      {if (true) return result;}
    throw new Error("Missing return statement in function");
  }

  final public Collection<AbstractRelation> tablesIDB() throws ParseException {
    Token t;
    Collection<AbstractRelation> result = new ArrayList<AbstractRelation>();
    List<AbstractArgument> args;
    String name;
    label_3:
    while (true) {
      t = jj_consume_token(IDENTIFIER);
      jj_consume_token(15);
            name = t.image;
            args = new ArrayList<AbstractArgument>();
      switch ((jj_ntk==-1)?jj_ntk():jj_ntk) {
      case IDENTIFIER:
        t = jj_consume_token(IDENTIFIER);
                                args.add(new AbstractArgument(t.image));
        break;
      case VARIABLE:
        t = jj_consume_token(VARIABLE);
                             args.add(new AbstractArgument(new Variable(t.image)));
        break;
      default:
        jj_la1[2] = jj_gen;
        jj_consume_token(-1);
        throw new ParseException();
      }
      label_4:
      while (true) {
        switch ((jj_ntk==-1)?jj_ntk():jj_ntk) {
        case 16:
          ;
          break;
        default:
          jj_la1[3] = jj_gen;
          break label_4;
        }
        jj_consume_token(16);
        switch ((jj_ntk==-1)?jj_ntk():jj_ntk) {
        case IDENTIFIER:
          t = jj_consume_token(IDENTIFIER);
                                   args.add(new AbstractArgument(t.image));
          break;
        case VARIABLE:
          t = jj_consume_token(VARIABLE);
                                 args.add(new AbstractArgument(new Variable(t.image)));
          break;
        default:
          jj_la1[4] = jj_gen;
          jj_consume_token(-1);
          throw new ParseException();
        }
      }
      jj_consume_token(17);
              result.add(new AbstractRelation(name,args));
      switch ((jj_ntk==-1)?jj_ntk():jj_ntk) {
      case IDENTIFIER:
        ;
        break;
      default:
        jj_la1[5] = jj_gen;
        break label_3;
      }
    }
      {if (true) return result;}
    throw new Error("Missing return statement in function");
  }

  final public Collection<Tgd> tgds() throws ParseException {
    Collection<Tgd> result = new ArrayList<Tgd>();
    Tgd tgd;
    label_5:
    while (true) {
      tgd = tgd();
                    result.add(tgd);
      switch ((jj_ntk==-1)?jj_ntk():jj_ntk) {
      case NEG:
      case IDENTIFIER:
        ;
        break;
      default:
        jj_la1[6] = jj_gen;
        break label_5;
      }
    }
      {if (true) return result;}
    throw new Error("Missing return statement in function");
  }

  final public Tgd tgd() throws ParseException {
    Collection<Literal> left;
    Atom right;
    Tgd tgd;
    left = conjunctiveQuery();
    jj_consume_token(18);
    right = atom();
    switch ((jj_ntk==-1)?jj_ntk():jj_ntk) {
    case 19:
      jj_consume_token(19);
      break;
    default:
      jj_la1[7] = jj_gen;
      ;
    }
      tgd = new Tgd(left,right);
      if (!tgd.isSafe()) {
        {if (true) throw generateParseException();}
      }
      {if (true) return tgd;}
    throw new Error("Missing return statement in function");
  }

  final public Collection<Literal> conjunctiveQuery() throws ParseException {
    Collection<Literal> result = new ArrayList<Literal>();
    Literal a;
    a = literal();
                  result.add(a);
    label_6:
    while (true) {
      switch ((jj_ntk==-1)?jj_ntk():jj_ntk) {
      case 16:
        ;
        break;
      default:
        jj_la1[8] = jj_gen;
        break label_6;
      }
      jj_consume_token(16);
      a = literal();
                        result.add(a);
    }
      {if (true) return result;}
    throw new Error("Missing return statement in function");
  }

  final public Atom atom() throws ParseException {
    String name;
    List<Value> args = new ArrayList<Value>();
    Value v;
    Token t;
    t = jj_consume_token(IDENTIFIER);
    jj_consume_token(15);
                         name = t.image;
    v = value();
                  args.add(v);
    label_7:
    while (true) {
      switch ((jj_ntk==-1)?jj_ntk():jj_ntk) {
      case 16:
        ;
        break;
      default:
        jj_la1[9] = jj_gen;
        break label_7;
      }
      jj_consume_token(16);
      v = value();
                       args.add(v);
    }
    jj_consume_token(17);
      {if (true) return new Atom(name, args);}
    throw new Error("Missing return statement in function");
  }

  final public Literal literal() throws ParseException {
    Atom a;
    Token t;
    switch ((jj_ntk==-1)?jj_ntk():jj_ntk) {
    case IDENTIFIER:
      a = atom();
               {if (true) return new Literal(a, true);}
      break;
    case NEG:
      jj_consume_token(NEG);
      a = atom();
                     {if (true) return new Literal(a, false);}
      break;
    default:
      jj_la1[10] = jj_gen;
      jj_consume_token(-1);
      throw new ParseException();
    }
    throw new Error("Missing return statement in function");
  }

  final public Value value() throws ParseException {
    Token t;
    switch ((jj_ntk==-1)?jj_ntk():jj_ntk) {
    case VARIABLE:
      t = jj_consume_token(VARIABLE);
                     {if (true) return new Variable(t.image);}
      break;
    case CONSTANT:
      t = jj_consume_token(CONSTANT);
                     {if (true) return Constant.parse(t.image);}
      break;
    default:
      jj_la1[11] = jj_gen;
      jj_consume_token(-1);
      throw new ParseException();
    }
    throw new Error("Missing return statement in function");
  }

  /** Generated Token Manager. */
  public MappingParserTokenManager token_source;
  SimpleCharStream jj_input_stream;
  /** Current token. */
  public Token token;
  /** Next token. */
  public Token jj_nt;
  private int jj_ntk;
  private int jj_gen;
  final private int[] jj_la1 = new int[12];
  static private int[] jj_la1_0;
  static {
      jj_la1_init_0();
   }
   private static void jj_la1_init_0() {
      jj_la1_0 = new int[] {0x10000,0x800,0x4800,0x10000,0x4800,0x800,0xa00,0x80000,0x10000,0x10000,0xa00,0x4400,};
   }

  /** Constructor with InputStream. */
  public MappingParser(java.io.InputStream stream) {
     this(stream, null);
  }
  /** Constructor with InputStream and supplied encoding */
  public MappingParser(java.io.InputStream stream, String encoding) {
    try { jj_input_stream = new SimpleCharStream(stream, encoding, 1, 1); } catch(java.io.UnsupportedEncodingException e) { throw new RuntimeException(e); }
    token_source = new MappingParserTokenManager(jj_input_stream);
    token = new Token();
    jj_ntk = -1;
    jj_gen = 0;
    for (int i = 0; i < 12; i++) jj_la1[i] = -1;
  }

  /** Reinitialise. */
  public void ReInit(java.io.InputStream stream) {
     ReInit(stream, null);
  }
  /** Reinitialise. */
  public void ReInit(java.io.InputStream stream, String encoding) {
    try { jj_input_stream.ReInit(stream, encoding, 1, 1); } catch(java.io.UnsupportedEncodingException e) { throw new RuntimeException(e); }
    token_source.ReInit(jj_input_stream);
    token = new Token();
    jj_ntk = -1;
    jj_gen = 0;
    for (int i = 0; i < 12; i++) jj_la1[i] = -1;
  }

  /** Constructor. */
  public MappingParser(java.io.Reader stream) {
    jj_input_stream = new SimpleCharStream(stream, 1, 1);
    token_source = new MappingParserTokenManager(jj_input_stream);
    token = new Token();
    jj_ntk = -1;
    jj_gen = 0;
    for (int i = 0; i < 12; i++) jj_la1[i] = -1;
  }

  /** Reinitialise. */
  public void ReInit(java.io.Reader stream) {
    jj_input_stream.ReInit(stream, 1, 1);
    token_source.ReInit(jj_input_stream);
    token = new Token();
    jj_ntk = -1;
    jj_gen = 0;
    for (int i = 0; i < 12; i++) jj_la1[i] = -1;
  }

  /** Constructor with generated Token Manager. */
  public MappingParser(MappingParserTokenManager tm) {
    token_source = tm;
    token = new Token();
    jj_ntk = -1;
    jj_gen = 0;
    for (int i = 0; i < 12; i++) jj_la1[i] = -1;
  }

  /** Reinitialise. */
  public void ReInit(MappingParserTokenManager tm) {
    token_source = tm;
    token = new Token();
    jj_ntk = -1;
    jj_gen = 0;
    for (int i = 0; i < 12; i++) jj_la1[i] = -1;
  }

  private Token jj_consume_token(int kind) throws ParseException {
    Token oldToken;
    if ((oldToken = token).next != null) token = token.next;
    else token = token.next = token_source.getNextToken();
    jj_ntk = -1;
    if (token.kind == kind) {
      jj_gen++;
      return token;
    }
    token = oldToken;
    jj_kind = kind;
    throw generateParseException();
  }


/** Get the next Token. */
  final public Token getNextToken() {
    if (token.next != null) token = token.next;
    else token = token.next = token_source.getNextToken();
    jj_ntk = -1;
    jj_gen++;
    return token;
  }

/** Get the specific Token. */
  final public Token getToken(int index) {
    Token t = token;
    for (int i = 0; i < index; i++) {
      if (t.next != null) t = t.next;
      else t = t.next = token_source.getNextToken();
    }
    return t;
  }

  private int jj_ntk() {
    if ((jj_nt=token.next) == null)
      return (jj_ntk = (token.next=token_source.getNextToken()).kind);
    else
      return (jj_ntk = jj_nt.kind);
  }

  private java.util.List<int[]> jj_expentries = new java.util.ArrayList<int[]>();
  private int[] jj_expentry;
  private int jj_kind = -1;

  /** Generate ParseException. */
  public ParseException generateParseException() {
    jj_expentries.clear();
    boolean[] la1tokens = new boolean[20];
    if (jj_kind >= 0) {
      la1tokens[jj_kind] = true;
      jj_kind = -1;
    }
    for (int i = 0; i < 12; i++) {
      if (jj_la1[i] == jj_gen) {
        for (int j = 0; j < 32; j++) {
          if ((jj_la1_0[i] & (1<<j)) != 0) {
            la1tokens[j] = true;
          }
        }
      }
    }
    for (int i = 0; i < 20; i++) {
      if (la1tokens[i]) {
        jj_expentry = new int[1];
        jj_expentry[0] = i;
        jj_expentries.add(jj_expentry);
      }
    }
    int[][] exptokseq = new int[jj_expentries.size()][];
    for (int i = 0; i < jj_expentries.size(); i++) {
      exptokseq[i] = jj_expentries.get(i);
    }
    return new ParseException(token, exptokseq, tokenImage);
  }

  /** Enable tracing. */
  final public void enable_tracing() {
  }

  /** Disable tracing. */
  final public void disable_tracing() {
  }

}
