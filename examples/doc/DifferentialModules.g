#! @System DifferentialModules

LoadPackage( "FunctorCategories" );

#! We illustrate how the category of functors can be used to model differential modules.
#! First, create a quiver $q$ with one edge 1 and one vertex $t$.

#! @Example
q := RightQuiver( "q(1)[t:1->1]" );
#! q(1)[t:1->1]
#! @EndExample

#! Construct the path algebra $\mathbb{Q}q$ of $q$.

#! @Example
Q := HomalgFieldOfRationals( );
#! Q
Qq := PathAlgebra( Q, q );
#! Q * q
#! @EndExample

#! Consider $\mathbb{Q}q$ as an algebroid $B$ with one object $1$ and morphisms given by $\mathbb{Q}q$.

#! @Example
B := Algebroid( Qq );
#! Algebra generated by the right quiver q(1)[t:1->1]
#! @EndExample

#! Define a record that described the $\mathbb{Q}$-linear morphism $\epsilon \colon B \to \mathbb{Q}$ defined by $\epsilon(t) = 0$.

#! @Example
counit := rec( t := 0 );
#! rec( t := 0 )
#! @EndExample

#! Construct the tensor product $B \otimes_{\mathbb{Q}} B$.

#! @Example
B2 := B^2;
#! Algebra generated by the right quiver qxq(1x1)[1xt:1x1->1x1,tx1:1x1->1x1]
#! @EndExample

#! Define a record that describes the $\mathbb{Q}$-linear morphism $\Delta \colon B \to B \otimes_{\mathbb{Q}} B$ defined by $\Delta(t) \coloneqq t \otimes 1 + 1 \otimes t$.

#! @Example
comult := rec( t := B2.tx1 + B2.1xt );
#! rec( t := (1x1)-[{ 1*(tx1) + 1*(1xt) }]->(1x1) )
#! @EndExample

#! Consider $B$ as a bialgebroid (which is actually a bialgebra) with respect to the counit $\epsilon$ and comultiplication $\Delta$.

#! @Example
AddBialgebroidStructure( B, counit, comult );
#! Bialgebra generated by the right quiver q(1)[t:1->1]
#! @EndExample

#! Retrieve the counit of $B$ as a functor

#! @Example
counit := Counit( B );
#! Functor from finitely presented Bialgebra generated by
#! the right quiver q(1)[t:1->1] -> Algebra generated by
#! the right quiver *(1)[]
#! @EndExample

#! Apply the functor counit to the (unique) object 1 of $B$.

#! @Example
ApplyFunctor( counit, B.1 );
#! (1)
#! @EndExample

#! When we apply the functor counit to the morphism $t$ of $B$, we obtain the zero endomorphism of the object $1$ of $B^0$.

#! @Example
ApplyFunctor( counit, B.t );
#! (1)-[0]->(1)
#! @EndExample

#! Retrieve the comultiplication of $B$ as a functor.

#! @Example
comult := Comultiplication( B );
#! Functor from finitely presented Bialgebra generated by
#! the right quiver q(1)[t:1->1] -> Algebra generated by
#! the right quiver qxq(1x1)[1xt:1x1->1x1,tx1:1x1->1x1]
ApplyFunctor( comult, B.1 );
#! (1x1)
#! @EndExample

#! When we apply the functor comult to the morphism $t$ of $B$, we obtain the endomorphism $t \otimes 1 + 1 \otimes t$ on the object $1 \times 1$ of $B^2$.

#! @Example
ApplyFunctor( comult, B.t );
#! (1x1)-[{ 1*(tx1) + 1*(1xt) }]->(1x1)
#! @EndExample

#! Define the underlying record for the antipode $S \colon B \to B$. It sends $t$ to $-t$.

#! @Example
antipode := rec( t := -B.t );
#! rec( t := (1)-[-1*(t)]->(1) )
#! @EndExample

#! Add the antipode to $B$.

#! @Example
AddAntipode( B, antipode );
#! @EndExample

#! Get the antipode back as a contravariant functor from $B$ to $B$.

#! @Example
antipode := Antipode( B );
#! Contravariant functor from finitely presented
#! Hopf algebra generated by the right quiver q(1)[t:1->1]
#! -> Hopf algebra generated by the right quiver q(1)[t:1->1]
ApplyFunctor( antipode, B.1 );
#! (1)
ApplyFunctor( antipode, B.t );
#! (1)-[-1*(t)]->(1)
#! @EndExample

#! Let $A$ be the category with objects the natural numbers and morphisms the matrices with coefficients in $\mathbb{Q}$.
#! We use it as a skeletal model of the category of finite dimension vector spaces.

#! @Example
LoadPackage( "LinearAlgebraForCAP" );
#! true
A := MatrixCategory( Q );
#! Category of matrices over Q
#! @EndExample

#! Let $H$ be the category of functors from $B$ to $A$.

#! @Example
H := Hom( B, A );
#! The category of functors: Hopf algebra generated by
#! the right quiver q(1)[t:1->1] -> Category of matrices over Q
#! @EndExample

#! Let $z$ be the zero object in $H$.

#! @Example
z := ZeroObject( H );
#! <A zero object in The category of functors: Hopf algebra generated by
#!  the right quiver q(1)[t:1->1] -> Category of matrices over Q>
z( B.1 );
#! <A vector space object over Q of dimension 0>
z( B.t );
#! <A zero, identity morphism in Category of matrices over Q>
#! @EndExample

#! Let $id_z$ be the identity morphism on $z$.

#! @Example
idz := IdentityMorphism( z );
#! <A zero, identity morphism in The category of functors: Hopf algebra
#!  generated by the right quiver q(1)[t:1->1] -> Category of matrices over Q>
idz( B.1 );
#! <A zero, identity morphism in Category of matrices over Q>
DirectSum( z, z );
#! <A zero object in The category of functors: Hopf algebra generated by
#!  the right quiver q(1)[t:1->1] -> Category of matrices over Q>
z = DirectSum(z,z);
#! true
#! @EndExample

#! Define a HomAlg matrix $\varphi$.

#! @Example
phi := HomalgMatrix( [ 0, 1, 0,  0, 0, 1,  1, 0, 0 ], 3, 3, Q );
#! <A 3 x 3 matrix over an internal ring>
#! @EndExample

#! Let $V$ be a $\mathbb{Q}$-vector space of dimension 3.

#! @Example
V := VectorSpaceObject( 3, Q );
#! <A vector space object over Q of dimension 3>
#! @EndExample

#! Construct a record that will be used to define a functor from $B$ to $A$.

#! @Example
V_obj := rec( 1 := V );
#! rec( 1 := <A vector space object over Q of dimension 3> )
V_mor := rec( t := VectorSpaceMorphism( V, phi, V ) );
#! rec( t := <A morphism in Category of matrices over Q> )
#! @EndExample

#! Finally construct a functor from $B$ to $A$ that sends the unique object $1$ of $B$ to the natural number 3 (representing a $\mathbb{Q}$-vector space of dimension 3) and the morphism $t$ in $B$ to the morphism induced by $\varphi$.
#! We call this functor again $V$.

#! @Example
V := AsObjectInHomCategory( B, V_obj, V_mor );
#! <An object in The category of functors: Hopf algebra generated by
#!  the right quiver q(1)[t:1->1] -> Category of matrices over Q>
#! @EndExample

#! Check whether $V$ is well-defined.

#! @Example
IsWellDefined( V );
#! true
#! @EndExample

#! The image of the object $1$ is the 3-dimensional $\mathbb{Q}$-vector space.

#! @Example
V( B.1 );
#! <A vector space object over Q of dimension 3>
#! @EndExample

#! The image of the morphism $t$ is the morphism induced by the matrix $\varphi$.

#! @Example
V( B.t );
#! <A morphism in Category of matrices over Q>
Display( V( B.t ) );
#! [ [  0,  1,  0 ],
#!   [  0,  0,  1 ],
#!   [  1,  0,  0 ] ]
#! 
#! A morphism in Category of matrices over Q
#! @EndExample

#! Verify that $V$ is not zero.

#! @Example
IsZero( V );
#! false
#! @EndExample

#! Compute the direct sum $W \coloneqq V \oplus V$.

#! @Example
W := DirectSum( V, V );
#! <An object in The category of functors: Hopf algebra generated by
#!  the right quiver q(1)[t:1->1] -> Category of matrices over Q>
W( B.1 );
#! <A vector space object over Q of dimension 6>
W( B.t );
#! <A morphism in Category of matrices over Q>
Display( W( B.t ) );
#! [ [  0,  1,  0,  0,  0,  0 ],
#!   [  0,  0,  1,  0,  0,  0 ],
#!   [  1,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  1,  0 ],
#!   [  0,  0,  0,  0,  0,  1 ],
#!   [  0,  0,  0,  1,  0,  0 ] ]
#! 
#! A morphism in Category of matrices over Q
#! @EndExample

#! Compute the projection $\pi_1$ from $V \oplus V$ to the first summand.

#! @Example
pi1 := ProjectionInFactorOfDirectSum( [ V, V ], 1 );
#! <A morphism in The category of functors: Hopf algebra generated by
#!  the right quiver q(1)[t:1->1] -> Category of matrices over Q>
pi1 = -pi1;
#! false
pi1( B.1 );
#! <A morphism in Category of matrices over Q>
Display( pi1( B.1 ) );
#! [ [  1,  0,  0 ],
#!   [  0,  1,  0 ],
#!   [  0,  0,  1 ],
#!   [  0,  0,  0 ],
#!   [  0,  0,  0 ],
#!   [  0,  0,  0 ] ]
#! 
#! A morphism in Category of matrices over Q
IsWellDefined( pi1 );
#! true
IsEpimorphism( pi1 );
#! true
IsMonomorphism( pi1 );
#! false
#! @EndExample

#! Compute the kernel object of the projection of $\pi_1$.

#! @Example
V1 := KernelObject( pi1 );
#! <An object in The category of functors: Hopf algebra generated by
#!  the right quiver q(1)[t:1->1] -> Category of matrices over Q>
IsWellDefined( V1 );
#! true
V1 = V;
#! true
#! @EndExample

#! Compute the projection $\pi_2$ from $V \oplus V$ to the second summand.

#! @Example
pi2 := ProjectionInFactorOfDirectSum( [ V, V ], 2 );
#! <A morphism in The category of functors: Hopf algebra generated by
#!  the right quiver q(1)[t:1->1] -> Category of matrices over Q>
pi1 = pi2;
#! false
#! @EndExample

#! Next we consider the monoidal structure on the category of functors from $B$ to $A$.
#! First we compute the unit object of this monoidal structure.

#! @Example
I := TensorUnit( H );
#! <An object in The category of functors: Hopf algebra generated by
#!  the right quiver q(1)[t:1->1] -> Category of matrices over Q>
I( B.1 );
#! <A vector space object over Q of dimension 1>
I( B.t );
#! <A morphism in Category of matrices over Q>
Display( I( B.t ) );
#! [ [  0 ] ]
#! 
#! A morphism in Category of matrices over Q
#! @EndExample

#! Compute the tensor product $V \otimes V$.

#! @Example
VV := TensorProductOnObjects( V, V );
#! <An object in The category of functors: Hopf algebra generated by
#!  the right quiver q(1)[t:1->1] -> Category of matrices over Q>
VV( B.1 );
#! <A vector space object over Q of dimension 9>
VV( B.t );
#! <A morphism in Category of matrices over Q>
Display( VV( B.t ) );
#! [ [  0,  1,  0,  1,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  1,  0,  1,  0,  0,  0,  0 ],
#!   [  1,  0,  0,  0,  0,  1,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  1,  0,  1,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  1,  0,  1,  0 ],
#!   [  0,  0,  0,  1,  0,  0,  0,  0,  1 ],
#!   [  1,  0,  0,  0,  0,  0,  0,  1,  0 ],
#!   [  0,  1,  0,  0,  0,  0,  0,  0,  1 ],
#!   [  0,  0,  1,  0,  0,  0,  1,  0,  0 ] ]
#! 
#! A morphism in Category of matrices over Q
#! @EndExample

#! Compute the dual $V^{\ast}$ of $V$.

#! @Example
Vs := DualOnObjects( V );
#! <An object in The category of functors: Hopf algebra generated by
#!  the right quiver q(1)[t:1->1] -> Category of matrices over Q>
Vs( B.1 );
#! <A vector space object over Q of dimension 3>
Vs( B.t );
#! <A morphism in Category of matrices over Q>
Display( Vs( B.t ) );
#! [ [   0,   0,  -1 ],
#!   [  -1,   0,   0 ],
#!   [   0,  -1,   0 ] ]
#! 
#! A morphism in Category of matrices over Q
#! @EndExample

#! Compute the morphism $V \to V^{\ast\ast}$.

#! @Example
epsilon := MorphismToBidual( V );
#! <A morphism in The category of functors: Hopf algebra generated by
#!  the right quiver q(1)[t:1->1] -> Category of matrices over Q>
#! @EndExample

#! Clearly the source of this morphism is (isomorphic to) $V$.

#! @Example
Source( epsilon ) = V;
#! true
#! @EndExample

#! But its range is also isomorphic to $V$.

#! @Example
Range( epsilon ) = V;
#! true
#! @EndExample

#! Compute the internal hom object $\operatorname{Hom}(V,V)$.

#! @Example
EndV := InternalHomOnObjects( V, V );
#! <An object in The category of functors: Hopf algebra generated by
#!  the right quiver q(1)[t:1->1] -> Category of matrices over Q>
#! @EndExample

#! Compute $V^{\ast} \otimes V$.

#! @Example
VsV := TensorProductOnObjects( Vs, V );
#! <An object in The category of functors: Hopf algebra generated by
#!  the right quiver q(1)[t:1->1] -> Category of matrices over Q>
#! @EndExample

#! Compute $V \otimes V^{\ast}$.

#! @Example
VVs := TensorProductOnObjects( V, Vs );
#! <An object in The category of functors: Hopf algebra generated by
#!  the right quiver q(1)[t:1->1] -> Category of matrices over Q>
#! @EndExample

#! We have $\operatorname{Hom}(V,V) = V^{\ast} \otimes V$, but not $\operatorname{Hom}(V,V) = V \otimes V^{\ast}$.

#! @Example
EndV = VsV;
#! true
EndV = VVs;
#! false
#! @EndExample

#! Construct an isomorphism $V^{\ast} \otimes V \to V \otimes V^{\ast}$.

#! @Example
beta := Braiding( Vs, V );
#! <A morphism in The category of functors: Hopf algebra generated by
#!  the right quiver q(1)[t:1->1] -> Category of matrices over Q>
Source( beta ) = VsV;
#! true
Range( beta ) = VVs;
#! true



#! @EndExample
