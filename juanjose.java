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

class Amount{

    //@ spec_public
    private int cents;
    //@ spec_public
    private int euros;
    
    //@ public invariant -100 < cents < 100;
    //@ public invariant cents < 0 && euros > 0 && cents > 0 && euros < 0;
   
    /*@ requires -100 < cents < 100;
      @ requires Integer.MIN_VALUE <= euros <= Integer.MAX_VALUE;
      @ requires cents < 0 && euros > 0 && cents > 0 && euros < 0;
      @ ensures this.euros == euros && this.cents == cents;   
    */
    public Amount(int euros, int cents){
      this.euros = euros;
      this.cents = cents;
    }
   
    /*@ requires 100 > cents > -100;
      @ requires Integer.MAX_VALUE > euros > Integer.MIN_VALUE;
      @ ensures \result != null;
      @ ensures Integer.MIN_VALUE < \result.euros <= Integer.MAX_VALUE && -100 < \result.cents < 100;
      @ ensures !(\result.cents > 0 && \result.euros < 0);
      @ ensures !(\result.cents < 0 && \result.euros > 0);      
    @*/
    public /*@ non_null @*/ Amount negate(){      
      return new Amount(-euros,-cents); //parametros invertidos
    } 
   
    /*@ requires a != null;
      @ requires a.cents >= 0;
      @ requires a.euros >= 0;
      @ ensures \result != null;
      @*/
    public /*@ non_null @*/ Amount subtract(Amount a){       
     return this.add(a.negate());
    }
   
    /*@ requires a != null;
      @ requires -100 < a.cents < 100;
      @ requires Integer.MIN_VALUE < (cents + a.cents) < Integer.MIN_VALUE;
      @ requires Integer.MIN_VALUE < (euros + a.euros) < Integer.MIN_VALUE;
      @ ensures \result != null;
      @ ensures -100 < \result.cents < 100;
      @ ensures \result.euros * 100 + \result.cents == a.euros * 100 + a.cents + this.euros * 100 + this.cents;
    */
    public /*@ non_null @*/ Amount add(Amount a){   
      int new_euros = euros + a.euros;      
      int new_cents = cents + a.cents;    
      
      //@ assert new_cents < 0 && new_euros == Integer.MAX_VALUE; 
      //@ assert new_cents >= 100 && new_euros == Integer.MAX_VALUE; 
      if (new_cents <= -100 ) {  // agregar el =         
         new_cents = new_cents + 100;
         new_euros = new_euros - 1;   
      } 
      if (new_cents >= 100 ) {  // agregar el =   
         new_cents = new_cents - 100;
         new_euros = new_euros + 1; // Incorrect symbol doing currency convertion
      } 
      if (new_cents < 0 && new_euros > 0) { 
          new_cents = new_cents + 100; 
          new_euros = new_euros - 1;
      } 
      if (new_cents > 0 && new_euros < 0) { // Menores strictos
          new_cents = new_cents - 100; 
          new_euros = new_euros + 1;
      }
      //@ assert -100 < new_cents < 100;
      return new Amount(new_euros,new_cents);
    }
   
    public /*@ non_null @*/ boolean equal(Amount a) {
      if (a==null) return false;
      else return (euros == a.euros && cents == a.cents);
    }
}
