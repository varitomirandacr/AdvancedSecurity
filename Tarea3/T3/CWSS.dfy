

method Main() {

    var baseFindig := funcBaseFinding(0.9, 1.0, 1.0, 1.0, 1.0);
    print baseFindig;
    print "\n";
    var attackSurface := funcAttackSurface(0.9, 1.0, 1.0, 1.0, 0.9, 1.0);
    print attackSurface;
    print "\n";
    var environmental := funcEnvironmental(0.9, 1.0, 1.0, 1.0, 1.0);
    print environmental;
    print "\n";

    var base : real := baseFindig * attackSurface * environmental;
    print base;

    print "\nTotal:";
    assert zero <= baseFindig <= hundred;
    assert zero <= attackSurface <= one;
    assert zero <= environmental <= one;
    var total := funcTotal(baseFindig, attackSurface, environmental);
    print total;
}

const hundred : real := 100.0;
const ninetyfive : real := 95.0;
const eigthy : real := 80.0;
const sixty : real := 60.0;
const fourty : real := 40.0;
const twenty : real := 20.0;
const fifteen : real := 15.0;
const ten : real := 10.0;
const five : real := 5.0;
const four : real := 4.0;
const three : real := 3.0;
const zero : real := 0.0;
const one : real := 1.0;
const twenty_multiplier : real := 0.05;
const minimum : real := 0.01;

method funcImpact(impact:real) returns (result:real)
    requires zero == impact || zero < impact <= one
    requires one == impact || zero <= impact < one
    ensures impact == zero ==> result == zero
    ensures impact != zero ==> result == one
    ensures zero == result || one == result
{
    assert zero == impact || zero < impact <= one;
    if impact == zero { result:= zero; } else { result:= one; }
    assert impact == zero ==> result == zero;
    assert impact != zero ==> result == one;
}

method funcBaseFinding(ti:real, ap:real, al:real, ic:real, fc:real) returns (baseFinding:real)
    requires zero <= ti <= one
    requires zero <= ap <= one
    requires zero <= al <= one
    requires zero <= ic <= one
    requires zero <= fc <= one
    ensures zero <= baseFinding <= hundred
{
    var fti := funcImpact(ti);
    var formulaBase := ((ten*ti) + (five*(ap+al)) + (five*fc));
    
    assert zero <= fti <= one;
    if (fti * ic == zero) { baseFinding := zero; }
    else if (fti * ic == one) { baseFinding := formulaBase * four; }
    else if ( fti == one && zero < ic <= one ) { baseFinding := (formulaBase * ic) * four; }

    if baseFinding < zero { baseFinding:= zero; } 
    else if baseFinding > hundred { baseFinding := hundred; }
    else { baseFinding := baseFinding; }   
}

method funcAttackSurface(rp:real, rl:real, av:real, asn:real, lin:real, sc:real) returns (attackSurface:real) 
    requires zero <= rp <= one
    requires zero <= rl <= one
    requires zero <= av <= one
    requires zero <= asn <= one
    requires zero <= lin <= one
    requires zero <= sc <= one
    ensures zero <= attackSurface <= one
{
    var accumulator := (twenty*rp);
    assert zero <= accumulator <= twenty;
    accumulator := accumulator + (twenty*rl);
    assert zero <= accumulator <= fourty;
    accumulator := accumulator + (twenty*av);
    assert zero <= accumulator <= sixty;
    accumulator := accumulator + (twenty*sc);
    assert zero <= accumulator <= eigthy;
    accumulator := accumulator + (fifteen*lin);
    assert zero <= accumulator <= ninetyfive;
    accumulator := accumulator + (five*asn);  
    assert zero <= accumulator <= hundred;  
    attackSurface := accumulator * minimum; 
    assert zero <= attackSurface <= one;  

    if attackSurface < zero { attackSurface:= zero; assert accumulator == zero; }
    else if attackSurface > one { attackSurface := one; assert accumulator == one; }
    else { attackSurface := attackSurface; assert zero <= attackSurface <= one; }
} 

method funcEnvironmental(bi:real, di:real, ex:real, ec:real, p:real) returns (environmental:real) 
    requires zero <= bi <= one 
    requires zero <= di <= one
    requires zero <= ex <= one
    requires zero <= ec <= one
    requires zero <= p <= one
    ensures zero <= environmental <= one
{
    var fbi := funcImpact(bi);
    assert bi == zero ==> bi == zero;
    assert zero == fbi || one == fbi;
    var formulaBase := (ten*bi) + (three*di) + (four*ex) + (three*p);
    assert zero <= formulaBase <= twenty;

    environmental := formulaBase;
    if (zero < fbi < one) { environmental := environmental * fbi; }
    if (zero < ec < one) { environmental := environmental * ec; }
    if (fbi * ec == zero) { environmental := zero; }
    else { environmental := environmental * twenty_multiplier; }
    
    if environmental < zero { environmental:= zero; assert environmental == zero; } 
    else if environmental > one { environmental := one; assert environmental == one; }
    else { environmental := environmental; assert zero <= environmental <= one; }    
} 

method funcTotal(finding:real, surface:real, env:real) returns (cwss:real)
    requires zero <= finding <= hundred;
    requires zero <= surface <= one;
    requires zero <= env <= one;
    ensures zero <= cwss <= hundred;
{
    cwss := finding * surface * env;
    if cwss < zero { cwss:= zero; assert cwss == zero; } 
    else if cwss > one { cwss := one; assert cwss == one; }
    else { cwss := cwss; assert zero <= cwss <= one; }    
}


