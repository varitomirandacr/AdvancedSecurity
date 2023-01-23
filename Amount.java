/*
 * This assignment is based on Erik Poll's assignment (Radboud University, Nijmegen).
 */

/* OpenJML exercise

   Objects of this class represent euro amounts. For example, an Amount 
   object with
     euros == 1
     cents == 55
   represents 1.55 euro. 

   Specify the class with JML and check it OpenJML.  

   NB there may be errors in the code that you have to fix to stop 
   OpenJML from complaining, as these complaints of OpenJML 
   point to real bugs in the code. But keep changes to the code to
   a minimum of what is strictly needed. 
   Mark any changes you have made in the code with a comment,
   eg to indicate that you replaced <= by <.

   You should add enough annotations to stop OpenJML complaining,
   but you should ALSO specify invariants discussed below:

   1) We do not want to represent 1.55 euro as an object with
         euro  == 0
         cents == 155
      (Note that the "equals" method will not be correct if we allow 
       this.)
      Specify an invariant that rules this out.

   2) We do not want to represent 1.55 euro as an object with
         euros =  2
         cents =  -45
      Specify one (or more) invariant(s) that rule this out. But note that
      we DO want to allow negative amounts, otherwise the method negate 
      can't be allowed.
      It may be useful to use the JML notation ==> (for implication) in 
      your invariants.

   While developing your specs, it may be useful to use the keywords
      assert
   to add additional assertions in source code, to find out what 
   OpenJML can - or cannot - prove at a given program point.

*/

public class Amount{

    //@ spec_public
    private int cents;    
    //@ spec_public
    private int euros;
   
    /*@ ensures this.euros == euros && this.cents == cents;
      @ ensures euros >= Integer.MIN_VALUE && euros <= Integer.MAX_VALUE;
      @ ensures cents >= Integer.MIN_VALUE && cents <= Integer.MAX_VALUE;
      @*/
    public Amount(int euros, int cents){
      this.euros = euros;
      this.cents = cents;
    }

    /*@ requires cents >= 0;
      @ requires euros >= 0;
      @ ensures \result != null;
      @ ensures Integer.MIN_VALUE < \result.euros <= 0;
      @ ensures Integer.MIN_VALUE < \result.cents <= 0;
      @*/
    public /*@ non_null @*/ Amount negate(){
      // BUG FIX: (-cents, -euros) a (-euros, -cents)
      // Valores invertidos el ctor pide primero los euros y luego los cents
      return new Amount(-euros, -cents);
    }    
    
    /* requires a != null;
      @ requires cents >= 0;
      @ requires euros >= 0;
       /requires a.euros > 0 && a.cents > 0;
       /requires this.euros > a.euros;
      @ ensures \result != null;
      @
    public testAmount subtract(testAmount a){
      return this.add(a.negate());
    }*/

    /*@ requires a != null;
      @ requires Integer.MIN_VALUE <= this.euros <= Integer.MAX_VALUE;
      @ requires Integer.MIN_VALUE <= this.cents <= Integer.MAX_VALUE;
      @ requires Integer.MIN_VALUE < (this.euros + a.euros) < Integer.MAX_VALUE;
      @ requires Integer.MIN_VALUE < (this.cents + a.cents) < Integer.MAX_VALUE;
      @ ensures \result != null;
      @*/
    public Amount add(/*@non_null@*/Amount a){
      int new_euros = euros + a.euros; 
      //@ assert Integer.MIN_VALUE < (new_euros) < Integer.MAX_VALUE;
      int new_cents = cents + a.cents; 
      //@ assert Integer.MIN_VALUE < (new_cents) < Integer.MAX_VALUE;

      // BUG FIX: de [< a <=]
      // Si no se incluye el = evaluaria hasta -99
      if (new_cents <= -100) {  
        new_cents = new_cents + 100;
        new_euros = new_euros - 1;
        //@ assert new_cents <= 100;
        //@ assert Integer.MIN_VALUE <= new_euros;
      } 
      // BUG FIX: de [> a >=]
      // Si no se incluye el = evaluaria hasta 99, caso contrario al de arriba
      if (new_cents >= 100) {  
        new_cents = new_cents - 100;
        // BUG FIX: de [- a +]
        // Cuando tenemos mas cents se restan los cents pero se deben incrementar los euros
        new_euros = new_euros + 1;
        //@ assert new_cents >= -100;
        //@ assert Integer.MAX_VALUE >= new_euros;
      } 
      if (new_cents < 0 && new_euros > 0) { 
        new_cents = new_cents + 100; 
        new_euros = new_euros - 1;
        //@ assert new_cents <= 100;
        //@ assert Integer.MIN_VALUE <= new_euros;
      } 
      // BUG FIX: de [>= y <= a > y <]
      // Si tenemos valores en cero no deberia ni quitar ni poner montos a ninguna variable
      if (new_cents > 0 && new_euros < 0) {
        new_cents = new_cents - 100; 
        new_euros = new_euros + 1;
        //@ assert new_cents >= -100;
        //@ assert Integer.MAX_VALUE >= new_euros;
      }
      return new Amount(new_euros, new_cents);
    }
   
    /*@ requires a != null;
      @ requires this.euros == a.euros;
      @ requires this.cents == a.cents;
      @ ensures \result == true || \result == false;
      @*/
    public boolean equal(/*@ non_null @*/ Amount a) {
      //@ assert Integer.MIN_VALUE <= this.euros <= Integer.MAX_VALUE;
      //@ assert Integer.MIN_VALUE <= this.cents <= Integer.MAX_VALUE;
      if (a==null) return false;
      else return (euros == a.euros && cents == a.cents);
    }
}
   