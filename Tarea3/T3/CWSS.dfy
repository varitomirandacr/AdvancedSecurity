

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
}

const hundred : real := 100.0;
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
    requires zero <= impact && impact <= one
    ensures impact == zero ==> result == zero
    ensures impact != zero ==> result == one
    ensures result >= zero && result <= one
{
    assert zero <= impact && impact <= one;
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
    assert zero <= fti <= one;
    
    baseFinding := zero;
    if (fti * ic > zero) {     
        baseFinding := (((ten*ti) + (five*(ap+al)) + (five*fc)) * ic) * four;
        
        if baseFinding < zero { baseFinding:= zero; } 
        else if baseFinding > hundred { baseFinding := hundred; }
        else { baseFinding := baseFinding; }
    }
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
    var block1 := (rp + rl + av);
    var block2 := (twenty * block1);
    var block3 := (twenty * sc);
    var block4 := (fifteen * lin);
    var block5 := (five * asn);
    var block6 := (block2 + block3);
    var block7 := (block6 + block4);
    var block8 := (block7 + block5);
    attackSurface := (block8 / hundred);
    assert zero <= attackSurface <= one ==> (attackSurface / hundred) <= one;   
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
    var result := (ten*bi) + (three*di) + (four*ex) + (three*p);

    if (fbi * ec == zero) { environmental := zero; }
    else if (fbi * ec == one) { environmental := result * twenty_multiplier; }
    else if fbi == one { environmental := (result * ec) * twenty_multiplier; }
    
    if environmental < zero { environmental:= zero; } 
    else if environmental > one { environmental := one; }
    else { environmental := environmental; }    
} 

method funcTotal(finding:real, surface:real, env:real) returns (cwss:real)
    requires one <= finding <= hundred;
    requires one <= surface <= one;
    requires one <= env <= one;
    ensures one <= cwss <= hundred;
{
    cwss := surface * hundred;
    assert zero <= cwss <= hundred;
    cwss := (cwss * finding) * minimum;
    assert zero <= cwss <= hundred;
    cwss := cwss * env;
    assert zero <= cwss <= hundred;

    print cwss;
}


