# SPDX-License-Identifier: GPL-2.0-or-later
# FunctorCategories: Categories of functors
#
# Implementations
#

BindGlobal( "FUNCTOR_CATEGORIES", rec( QQ := HomalgFieldOfRationals( ) ) );

##
InstallMethod( IsomorphismFromCategoryOfQuiverRepresentations,
          [ IsCapHomCategory ],
  function ( functors )
    local B, matrix_cat, field, A, quiver, quiver_reps, name, F;
    
    B := Source( functors );
    
    matrix_cat := Range( functors );
    
    if not IsBound( matrix_cat!.field_for_matrix_category ) then
      
      Error( "The range category of the input should be a matrix category for some homalg field!\n" );
      
    fi;
    
    field := CommutativeRingOfLinearCategory( matrix_cat );
    
    A := UnderlyingQuiverAlgebra( B );
    
    quiver := QuiverOfAlgebra( A );
    
    quiver_reps := CategoryOfQuiverRepresentations( A );
    
    name := Concatenation( "Isomorphism functor from ", Name( quiver_reps ), " into ", Name( functors ) );
    
    F := CapFunctor( name, quiver_reps, functors );
    
    AddObjectFunction( F,
      function ( rep )
        local obj, dimension_vec, mor, matrices, i;
        
        obj := rec( );
        
        dimension_vec := DimensionVector( rep );
        
        for i in [ 1 .. Size( dimension_vec ) ] do
          
          obj!.(String( Vertex( quiver, i ) )) := VectorSpaceObject( dimension_vec[i], field );
          
        od;
        
        mor := rec( );
        
        matrices := MatricesOfRepresentation( rep );
        
        matrices := List( matrices,
          mat -> HomalgMatrix(
                    RowsOfMatrix( mat ),
                      DimensionsMat( mat )[ 1 ],
                        DimensionsMat( mat )[ 2 ], field ) );
                        
        for i in [ 1 .. Size( matrices ) ] do
          
          mor!.(String( Arrow( quiver, i ) )) :=
            VectorSpaceMorphism(
              obj!.(String( Source( Arrow( quiver, i ) ) )),
                matrices[i],
                  obj!.(String( Target( Arrow( quiver, i ) ) )) );
                  
        od;
        
        return AsObjectInHomCategory( B, obj, mor );
        
    end );
    
    AddMorphismFunction( F,
      function ( source, rep_mor, range )
        local matrices, mor, i;
        
        matrices := MatricesOfRepresentationHomomorphism( rep_mor );
        
        matrices := List( matrices,
          mat -> HomalgMatrix(
                    RowsOfMatrix( mat ),
                      DimensionsMat( mat )[ 1 ],
                        DimensionsMat( mat )[ 2 ], field ) );
                        
        mor := rec( );
        
        for i in [ 1 .. Size( matrices ) ] do
          
          mor!.(String( Vertex( quiver, i ) )) :=
            VectorSpaceMorphism(
              VectorSpaceObject( NrRows( matrices[i] ), field ),
                matrices[i],
                  VectorSpaceObject( NrColumns( matrices[i] ), field ) );
                  
        od;
        
        return AsMorphismInHomCategory( source, mor, range );
        
    end );
    
    return F;
    
end );

##
InstallMethod( IsomorphismOntoCategoryOfQuiverRepresentations,
          [ IsCapHomCategory ],
  function ( functors )
    local B, matrix_cat, A, field, quiver, quiver_reps, name, G;
    
    B := Source( functors );
    
    matrix_cat := Range( functors );
    
    if not IsBound( matrix_cat!.field_for_matrix_category ) then
      
      Error( "The range category of the input should be a matrix category for some homalg field!\n" );
      
    fi;
    
    A := UnderlyingQuiverAlgebra( B );
    
    field := LeftActingDomain( A );
    
    quiver := QuiverOfAlgebra( A );
    
    quiver_reps := CategoryOfQuiverRepresentations( A );
    
    name := Concatenation( "Isomorphism functor from ", Name( functors ), " into ", Name( quiver_reps ) );
    
    G := CapFunctor( name, functors, quiver_reps );
    
    AddObjectFunction( G,
      function ( func )
        local U, V, L;
        
        U := UnderlyingCapTwoCategoryCell( func );
        
        V := List( Vertices( quiver ),
          v -> Dimension( ApplyFunctor( U, B.( String( v ) ) ) ) );
          
        if IsHomalgExternalRingRep( matrix_cat!.field_for_matrix_category ) then
          
          L := List( Arrows( quiver ),
                l -> UnderlyingMatrix( ApplyFunctor( U, B.( String( l ) ) ) ) * FUNCTOR_CATEGORIES!.QQ
                );
                
        else
          
          L := List( Arrows( quiver ), l -> UnderlyingMatrix( ApplyFunctor( U, B.( String( l ) ) ) ) );
          
        fi;
        
        L := List( L,
              l -> MatrixByRows(
                field, [ NrRows( l ), NrColumns( l ) ],
                  EntriesOfHomalgMatrixAsListList( l ) ) );
                  
        return QuiverRepresentation( A, V, L );
        
      end );
      
    AddMorphismFunction( G,
      function ( source, mor, range )
        local U, V;
        
        U := UnderlyingCapTwoCategoryCell( mor );
        
        if IsHomalgExternalRingRep( matrix_cat!.field_for_matrix_category ) then
          
          V := List( Vertices( quiver ),
                v -> UnderlyingMatrix(
                  ApplyNaturalTransformation( U, B.( String( v ) ) ) ) * FUNCTOR_CATEGORIES!.QQ
                );
                
        else
          
          V := List( Vertices( quiver ),
                v -> UnderlyingMatrix(
                  ApplyNaturalTransformation( U, B.( String( v ) ) ) ) );
                   
        fi;
        
        V := List( V,
          v -> MatrixByRows( field, [ NrRows( v ), NrColumns( v ) ],
            EntriesOfHomalgMatrixAsListList( v ) ) );
            
        return QuiverRepresentationHomomorphism( source, range, V );
        
      end );
      
    return G;
    
end );

##
InstallMethod( YonedaEmbedding,
          [ IsAlgebroid ],
  function ( algebroid )
    local k, matrix_cat, algebroid_op, objs, mors, functors_cat, name, Yoneda;
    
    k := CommutativeRingOfLinearCategory( algebroid );
    
    matrix_cat := MatrixCategory( k );
    
    algebroid_op := OppositeAlgebroidOverOppositeQuiverAlgebra( algebroid );
    
    objs := SetOfObjects( algebroid_op );
    
    mors := SetOfGeneratingMorphisms( algebroid_op );
    
    functors_cat := Hom( algebroid_op, matrix_cat );
    
    name := "Yoneda embedding functor";
    
    Yoneda := CapFunctor( name, algebroid, functors_cat );
    
    AddObjectFunction( Yoneda,
      function ( o )
        local m, Yo;
        
        o := OppositePath( UnderlyingVertex( o ) ) / algebroid_op;
        
        m := List( mors, mor -> HomStructure( o, mor ) );
        
        o := List( objs, obj -> HomStructure( o, obj ) );
        
        Yo := AsObjectInHomCategory( algebroid_op, o, m );
        
        SetIsProjective( Yo, true );
        
        return Yo;
        
    end );
    
    AddMorphismFunction( Yoneda,
      function ( s, m, r )
        
        m := MorphismInAlgebroid(
                OppositePath( UnderlyingVertex( Range( m ) ) ) / algebroid_op,
                OppositeAlgebraElement( UnderlyingQuiverAlgebraElement( m ) ),
                OppositePath( UnderlyingVertex( Source( m ) ) ) / algebroid_op
              );
        
        m := List( objs, o -> HomStructure( m, o ) );
        
        return AsMorphismInHomCategory( s, m, r );
        
    end );
    
    return Yoneda;
    
end );

##
InstallMethod( YonedaIsomorphism,
          [ IsAlgebroid ],
  
  function( algebroid )
    local Y, indec_projs, name, Z;
    
    Y := YonedaEmbedding( algebroid );
    
    indec_projs := FullSubcategoryGeneratedByIndecProjectiveObjects( RangeOfFunctor( Y ) );
    
    name := "Yoneda isomorphism";
    
    Z := CapFunctor( name, algebroid, indec_projs );
    
    AddObjectFunction( Z, o -> AsSubcategoryCell( indec_projs, ApplyFunctor( Y, o ) ) );
    
    AddMorphismFunction( Z, { s, m, r } -> AsSubcategoryCell( indec_projs, ApplyFunctor( Y, m ) ) );
    
    return Z;
    
end );

##
InstallMethod( InverseOfYonedaIsomorphism,
          [ IsAlgebroid ],
          
  function( algebroid )
    local Y, indec_projs, name, object_func, morphism_func;
    
    Y := YonedaIsomorphism( algebroid );
    
    indec_projs := List( SetOfKnownObjects( RangeOfFunctor( Y ) ), UnderlyingCell );
    
    name := "Inverse of Yoneda isomorphism";
    
    object_func :=
      function( P )
        local i;
        
        P := UnderlyingCell( P );
        
        i := PositionProperty( indec_projs, Q -> ValuesOnAllObjects( Q ) = ValuesOnAllObjects( P ) );
        
        return ObjectInAlgebroid( algebroid, Vertex( UnderlyingQuiver( algebroid ), i ) );
        
      end;
      
    morphism_func :=
      function( eta )
        local s, r, B, YB, dim, rel;
        
        s := object_func( Source( eta ) );
        
        r := object_func( Range( eta ) );
        
        B := BasisOfExternalHom( s, r );
        
        YB := List( B, b -> UnderlyingCell( ApplyFunctor( Y, b ) ) );
        
        rel := Concatenation( [ UnderlyingCell( eta ) ], YB );
        
        rel := KernelEmbedding( MorphismBetweenDirectSums( List( rel, m -> [ HomStructure( m ) ] ) ) );
        
        rel := EntriesOfHomalgMatrixAsListList( UnderlyingMatrix( rel ) );
        
        if Size( rel ) > 1 then
        
          Error( "This should not happen!\n" );
          
        else
          
          rel := rel[ 1 ];
          
        fi;
        
        rel := AdditiveInverse( Inverse( rel[ 1 ] ) ) * rel;
        
        rel := rel{ [ 2 .. Size( B ) + 1 ] };
        
        if IsEmpty( rel ) then
          
          return ZeroMorphism( s, r );
          
        else
          
          return rel * B;
          
        fi;
        
      end;
      
    return FunctorFromLinearCategoryByTwoFunctions( name, RangeOfFunctor( Y ), algebroid, object_func, morphism_func );

end );

##
InstallMethod( DecompositionFunctorOfProjectiveObjects,
          [ IsCapHomCategory ],
          
  function( H )
    local projs, indec_projs, indec_projs_plus, name, Dec;
    
    projs := FullSubcategoryGeneratedByProjectiveObjects( H );
    
    indec_projs := FullSubcategoryGeneratedByIndecProjectiveObjects( H );
    
    indec_projs_plus := AdditiveClosure( indec_projs );
    
    #DeactivateCachingOfCategory( indec_projs_plus );
    
    name := "Decomposition equivalence";
    
    Dec := CapFunctor( name, projs, indec_projs_plus );
    
    AddObjectFunction( Dec,
      function( F )
        local dec;
        
        dec := DirectSumDecompositionOfProjectiveObject( UnderlyingCell( F ) );
        
        if IsEmpty( dec ) then
          
          return ZeroObject( indec_projs_plus );
          
        else
        
          dec := List( dec, m -> AsSubcategoryCell( indec_projs, Source( m ) ) );
        
          return AdditiveClosureObject( dec, indec_projs_plus );
          
        fi;
      
    end );
    
    
    AddMorphismFunction( Dec,
      function( s, eta, r )
        local dec_source, dec_range, iso_range, mat;
         
        if IsZeroForObjects( s ) or IsZeroForObjects( r ) then
          
          return ZeroMorphism( s, r );
          
        fi;
        
        eta := UnderlyingCell( eta );
        
        dec_source := DirectSumDecompositionOfProjectiveObject( Source( eta ) );
        
        dec_range := DirectSumDecompositionOfProjectiveObject( Range( eta ) );
        
        dec_range := List( dec_range, Source );
        
        iso_range := IsomorphismOntoDirectSumDecompositionOfProjectiveObject( Range( eta ) );
        
        if HasIsIdenticalToIdentityMorphism( iso_range ) and IsIdenticalToIdentityMorphism( iso_range ) then
          
          dec_range := List( [ 1 .. Size( dec_range ) ],
                          i -> ProjectionInFactorOfDirectSumWithGivenDirectSum( dec_range, i, Range( iso_range ) )
                        );
                        
        else
          
          dec_range := List( [ 1 .. Size( dec_range ) ],
                          i -> PreCompose(
                                  iso_range,
                                  ProjectionInFactorOfDirectSumWithGivenDirectSum( dec_range, i, Range( iso_range ) )
                              )
                        );
                        
        fi;
        
        mat := List( dec_source, u -> List( dec_range, v -> PreCompose( [ u, eta, v ] ) ) );
        
        mat := List( mat, row -> List( row, m -> AsSubcategoryCell( indec_projs, m ) ) );
        
        return AdditiveClosureMorphism( s, mat, r );
        
    end );
    
    return Dec;
    
end );

##
InstallMethod( RadicalFunctorAttr,
          [ IsCapHomCategory ],
          
  function( Hom )
    local rad;
    
    rad := CapFunctor( "Radical endofunctor", Hom, Hom );
    
    AddObjectFunction( rad,
      F -> Source( RadicalInclusion( F ) )
    );
    
    AddMorphismFunction( rad,
      { s, eta, r } -> LiftAlongMonomorphism(
                          PreCompose( RadicalInclusion( Source( eta ) ), eta ),
                          RadicalInclusion( Range( eta ) )
                        )
    );
    
    return rad;
    
end );

##
InstallMethod( RadicalFunctor, [ IsCapHomCategory ], RadicalFunctorAttr );
