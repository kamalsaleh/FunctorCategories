

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
