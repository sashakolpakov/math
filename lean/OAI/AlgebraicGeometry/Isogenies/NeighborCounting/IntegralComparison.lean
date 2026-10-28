import OAI.AlgebraicGeometry.AbelianScheme.HomExtension
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Isogeny.BaseChange
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.BaseChange

/-! # Integral Comparison -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntegralComparison

noncomputable section

/-!
Good-reduction comparisons from generic fibers. A generic group isomorphism
extends to an actual integral group isomorphism by HomExtension. Equality of the
polarization and integral-action maps extends by schematic density and
can then be restricted to the special fiber.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

attribute [local instance] AbelianScheme.FrobeniusKernel.BaseChange.Construction.pulledBackGroup

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]

abbrev genericMap : Spec (.of K) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R K))

variable {a b : ℕ}
variable (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a (Spec (.of R))) (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme b (Spec (.of R)))

def extendHom (f : (A.pullback (genericMap (R := R) (K := K))).scheme ⟶
    (B.pullback (genericMap (R := R) (K := K))).scheme) [IsMonHom f] :
    A.scheme ⟶ B.scheme :=
  (AbelianScheme.HomExtension.neron_extension_of_abelian_hom A.scheme B.scheme f
    (inferInstanceAs (IsMonHom f))).choose

instance extendHom_isMonHom
    (f : (A.pullback (genericMap (R := R) (K := K))).scheme ⟶
      (B.pullback (genericMap (R := R) (K := K))).scheme) [IsMonHom f] :
    IsMonHom (extendHom A B f) :=
  (AbelianScheme.HomExtension.neron_extension_of_abelian_hom A.scheme B.scheme f
    (inferInstanceAs (IsMonHom f))).choose_spec.1.1

theorem extendHom_generic
    (f : (A.pullback (genericMap (R := R) (K := K))).scheme ⟶
      (B.pullback (genericMap (R := R) (K := K))).scheme) [IsMonHom f] :
    (Over.pullback (genericMap (R := R) (K := K))).map (extendHom A B f) = f :=
  (AbelianScheme.HomExtension.neron_extension_of_abelian_hom A.scheme B.scheme f
    (inferInstanceAs (IsMonHom f))).choose_spec.1.2

/-- A generic comparison of good abelian schemes is an integral comparison;
both inverse identities are proved by generic-fiber injectivity. -/
def extendIso
    (e : (A.pullback (genericMap (R := R) (K := K))).scheme ≅
      (B.pullback (genericMap (R := R) (K := K))).scheme) [IsMonHom e.hom] :
    A.scheme ≅ B.scheme where
  hom := extendHom A B e.hom
  inv := extendHom B A e.inv
  hom_inv_id := by
    apply AbelianScheme.HomExtension.generic_fiber_map_injective (K := K) A.scheme A.scheme
    rw [Functor.map_comp, extendHom_generic, extendHom_generic]
    exact e.hom_inv_id.trans ((Over.pullback (genericMap (R := R) (K := K))).map_id _).symm
  inv_hom_id := by
    apply AbelianScheme.HomExtension.generic_fiber_map_injective (K := K) B.scheme B.scheme
    rw [Functor.map_comp, extendHom_generic, extendHom_generic]
    exact e.inv_hom_id.trans ((Over.pullback (genericMap (R := R) (K := K))).map_id _).symm

instance extendIso_isMonHom
    (e : (A.pullback (genericMap (R := R) (K := K))).scheme ≅
      (B.pullback (genericMap (R := R) (K := K))).scheme) [IsMonHom e.hom] :
    IsMonHom (extendIso A B e).hom := inferInstanceAs (IsMonHom (extendHom A B e.hom))

variable {A B}

theorem pullback_pow {S T : Scheme.{u}} (f : T ⟶ S)
    {X Y : Over S} [GrpObj Y] (p : X ⟶ Y) (n : ℕ) :
    (Over.pullback f).map (p ^ n) = ((Over.pullback f).map p) ^ n :=
  ((Over.pullback f).homMonoidHom).map_pow p n

omit [IsDiscreteValuationRing R] in
/-- The polarization multiplier equation extends from the characteristic-zero
fiber as an equality of actual integral morphisms. -/
theorem polarization_equation_extends
    {AD : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a (Spec (.of R))} {BD : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme b (Spec (.of R))}
    (f : A.scheme ⟶ B.scheme) (fd : BD.scheme ⟶ AD.scheme)
    (p : A.scheme ⟶ AD.scheme) (r : B.scheme ⟶ BD.scheme) (n : ℕ)
    (hgeneric :
      (Over.pullback (genericMap (R := R) (K := K))).map f ≫
        (Over.pullback (genericMap (R := R) (K := K))).map r ≫
        (Over.pullback (genericMap (R := R) (K := K))).map fd =
      ((Over.pullback (genericMap (R := R) (K := K))).map p) ^ n) :
    f ≫ r ≫ fd = p ^ n := by
  apply AbelianScheme.HomExtension.generic_fiber_map_injective (K := K) A.scheme AD.scheme
  simpa only [Functor.map_comp, pullback_pow] using hgeneric

omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem polarization_equation_specializes
    {AD : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a (Spec (.of R))} {BD : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme b (Spec (.of R))}
    (f : A.scheme ⟶ B.scheme) (fd : BD.scheme ⟶ AD.scheme)
    (p : A.scheme ⟶ AD.scheme) (r : B.scheme ⟶ BD.scheme) (n : ℕ)
    {T : Scheme.{u}} (s : T ⟶ Spec (.of R))
    (h : f ≫ r ≫ fd = p ^ n) :
    (Over.pullback s).map f ≫ (Over.pullback s).map r ≫ (Over.pullback s).map fd =
      ((Over.pullback s).map p) ^ n := by
  simpa only [Functor.map_comp, pullback_pow] using congrArg (Over.pullback s).map h

omit [IsDiscreteValuationRing R] in
/-- Integral endomorphism equivariance follows from its generic identity. -/
theorem action_equation_extends (f : A.scheme ⟶ B.scheme)
    (a : A.scheme ⟶ A.scheme) (b : B.scheme ⟶ B.scheme)
    (hgeneric :
      (Over.pullback (genericMap (R := R) (K := K))).map a ≫
        (Over.pullback (genericMap (R := R) (K := K))).map f =
      (Over.pullback (genericMap (R := R) (K := K))).map f ≫
        (Over.pullback (genericMap (R := R) (K := K))).map b) : a ≫ f = f ≫ b := by
  apply AbelianScheme.HomExtension.generic_fiber_map_injective (K := K) A.scheme B.scheme
  simpa only [Functor.map_comp] using hgeneric

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntegralComparison
