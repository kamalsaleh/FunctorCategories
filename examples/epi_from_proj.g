proj_cover :=
  function( a )
    local cat, new_a, morphism_from_new_a, maps, projs, hom, m, epi, p;
    cat := CapCategory( a );
    
    new_a := a;
    morphism_from_new_a := IdentityMorphism( a );
    maps := [ ];
    
    projs := ShallowCopy( IndecProjectiveObjects( cat ) );
    
    # ?Sort( projs, { p, q } -> IsEmpty( BasisOfExternalHom( p, q ) ) );
    
    for p in projs do
      
      hom := BasisOfExternalHom( p, new_a );
      
      if IsEmpty( hom ) then
        
        continue;
        
      fi;
      
      maps := Concatenation( maps, List( hom, h -> PreCompose( h, morphism_from_new_a ) ) );
      
      m := MorphismBetweenDirectSums( List( hom, h -> [ h ] ) );
      
      epi := CokernelProjection( m );
      
      new_a := Range( epi );
      
      morphism_from_new_a := PreCompose( Lift( IdentityMorphism( new_a ), epi ), morphism_from_new_a );
    
    od;
    
    return MorphismBetweenDirectSums( TransposedMat( [ maps ] ) );
    
  end;
