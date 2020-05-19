




##
InstallMethod( RadicalInclusion,
          [ IsCapCategoryObjectInHomCategory ],
          
  function( F )
    local algebroid, objs, mors, val_objs, val_mors, pos, im, RF;
    
    algebroid := SourceOfFunctor( UnderlyingCapTwoCategoryCell( F ) );
    
    objs := SetOfObjects( algebroid );
    
    mors := SetOfGeneratingMorphisms( algebroid );
    
    val_objs := ValuesOnAllObjects( F );
    
    val_mors := ValuesOnAllGeneratingMorphisms( F );
    
    pos := List( objs, o -> PositionsProperty( mors, m -> IsEqualForObjects( o, Range( m ) ) ) );
    
    im := List( pos, p -> val_mors{ p } );
    
    im :=
      ListN( im, val_objs,
        function( l, o )
          if IsEmpty( l ) then
            return UniversalMorphismFromZeroObject( o );
          else
            return ImageEmbedding( MorphismBetweenDirectSums( TransposedMat( [ l ] ) ) );
          fi;
        end
      );
      
    val_objs := List( im, Source );
    
    val_mors :=
      ListN( mors, val_mors,
        function( m, vm )
          local s, r;
          s := Position( objs, Source( m ) );
          r := Position( objs, Range( m ) );
          return LiftAlongMonomorphism( im[ r ], PreCompose( im[ s ], vm ) );
        end
      );
      
    RF := AsObjectInHomCategory( algebroid, val_objs, val_mors );
    
    return AsMorphismInHomCategory( RF, im, F );
    
end );

##
InstallMethod( CoverElementByProjectiveObject,
          [ IsCapCategoryObjectInHomCategory, IsCapCategoryMorphism, IsInt ],
  function( F, l, n )
    local functors_cat, algebroid, vertices, v, P_v, val_objs;
    
    functors_cat := CapCategory( F );
    
    algebroid := Source( functors_cat );
    
    vertices := SetOfObjects( algebroid );
     
    v := vertices[ n ];
     
    P_v := IndecProjectiveObjects( functors_cat )[ n ];
    
    val_objs := List( vertices, u -> List( BasisOfExternalHom( v, u ), b -> PreCompose( l, F( b ) ) ) );
    
    val_objs := ListN(
                  ValuesOnAllObjects( P_v ),
                  val_objs,
                  ValuesOnAllObjects( F ),
                  { s, rows, r } -> MorphismBetweenDirectSums( s, TransposedMat( [ rows ] ), r )
                );
                
    return AsMorphismInHomCategory( P_v, val_objs, F );
    
end );

##
InstallMethod( ProjectiveCover,
          [ IsCapCategoryObjectInHomCategory ],
  function( F )
    local functors_cat, matrix_cat, k, i_F, pi_i_F, pre_images, covers, p_F;
    
    functors_cat := CapCategory( F );
    
    matrix_cat := Range( functors_cat );
    
    k := 1 / matrix_cat;
    
    i_F := RadicalInclusion( F );
    
    pi_i_F := CokernelProjection( i_F );
    
    pre_images := List( ValuesOnAllObjects( pi_i_F ), m -> Lift( IdentityMorphism( Range( m ) ), m ) );
    
    covers :=
      ListN( pre_images, [ 1 .. Length( pre_images ) ],
        function( pre_image, i )
          local m, n, D, iotas;
          
          n := Dimension( Source( pre_image ) );
          
          D := ListWithIdenticalEntries( n, k );
          
          iotas := List( [ 1 .. n ], j -> PreCompose( InjectionOfCofactorOfDirectSum( D, j ), pre_image ) );
          
          return List( iotas, iota -> CoverElementByProjectiveObject( F, iota, i ) );
          
        end
      );
      
    covers := Concatenation( covers );
    
    p_F := MorphismBetweenDirectSums( TransposedMat( [ covers ] ) );
    
    # save summands
    
    return p_F;
    
end );
