import OAI.AlgebraicGeometry.PELModuli.CMPoints.EndomorphismParameterDescent

/-! # Presentations Tuple Parameters -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.PresentationsTupleParameters

noncomputable section

/-! Natural encoding and decoding of actual endomorphism tuples in an
Presentations locus. These identities are checked independently of arithmetic
descent, keeping the latter proof small in the kernel. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem e34_endomorphismEquiv_restrict {S : Scheme} {g : ℕ}
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) {T U : Over S} (b : T ⟶ U)
    (r : IntegralModel.Finite.Actions.GroupEndRing (A.pullback U.hom)) :
    IntegralModel.Presentations.EndomorphismBridge.EndomorphismFamilies.e34EndomorphismEquiv A T (IntegralModel.EndomorphismFamiliesId.EndomorphismFamilies.restrict A b r) =
      (HilbertScheme.Presentations.Endomorphisms.Core.endomorphismSubfunctor A.scheme).toFunctor.map b.op
        (IntegralModel.Presentations.EndomorphismBridge.EndomorphismFamilies.e34EndomorphismEquiv A U r) := by
  apply Subtype.ext
  exact IntegralModel.EndomorphismHom.EndomorphismFamilies.relativeHom_restrict A b r

variable {S : Scheme.{0}} {g n : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  {B : HilbertScheme.Presentations.Has.Core.ProjectivePresentation (A.scheme ⨯ A.scheme)}
  {P : Fin n → Polynomial ℚ}
  {L : HilbertScheme.Presentations.Loci.Core.HilbertHomLoci A.scheme A.scheme B n P}
  {R : HilbertScheme.Presentations.Endomorphisms.Core.FiniteEndomorphismEquations A.scheme n}
  (M : HilbertScheme.Presentations.Loci.Core.EndomorphismEquationLoci A.scheme B n P L R)

def e34TuplePoint (T : Over S) (r : Fin n → IntegralModel.Finite.Actions.GroupEndRing (A.pullback T.hom))
    (hr : HilbertScheme.Presentations.Has.Core.HasGraphPolynomials A.scheme A.scheme n B P
      (fun i => IntegralModel.EndomorphismHom.EndomorphismFamilies.relativeHomEquiv A T ((r i).hom _))) : T ⟶ M.endScheme :=
  (M.endEquivalence.app (.op T)).inv
    ⟨fun i => IntegralModel.Presentations.EndomorphismBridge.EndomorphismFamilies.e34EndomorphismEquiv A T (r i), (M.end_mem T _).mpr hr⟩

def e34TupleValue (T : Over S) (p : T ⟶ M.endScheme) :
    Fin n → IntegralModel.Finite.Actions.GroupEndRing (A.pullback T.hom) :=
  fun i => (IntegralModel.Presentations.EndomorphismBridge.EndomorphismFamilies.e34EndomorphismEquiv A T).symm
    (((M.endEquivalence.app (.op T)).hom p).val i)

theorem e34TupleValue_point (T : Over S)
    (r : Fin n → IntegralModel.Finite.Actions.GroupEndRing (A.pullback T.hom))
    (hr : HilbertScheme.Presentations.Has.Core.HasGraphPolynomials A.scheme A.scheme n B P
      (fun i => IntegralModel.EndomorphismHom.EndomorphismFamilies.relativeHomEquiv A T ((r i).hom _))) (i : Fin n) :
    e34TupleValue A M T (e34TuplePoint A M T r hr) i = r i := by
  let w : M.endLocus.toFunctor.obj (.op T) :=
    ⟨fun j => IntegralModel.Presentations.EndomorphismBridge.EndomorphismFamilies.e34EndomorphismEquiv A T (r j), (M.end_mem T _).mpr hr⟩
  have hw := (M.endEquivalence.app (.op T)).inv_hom_id_apply w
  exact (congrArg (fun v : M.endLocus.toFunctor.obj (.op T) =>
    (IntegralModel.Presentations.EndomorphismBridge.EndomorphismFamilies.e34EndomorphismEquiv A T).symm (v.val i)) hw).trans
      ((IntegralModel.Presentations.EndomorphismBridge.EndomorphismFamilies.e34EndomorphismEquiv A T).symm_apply_apply (r i))

theorem e34Locus_restriction {T U : Over S} (b : T ⟶ U) (p : U ⟶ M.endScheme) :
    M.endLocus.toFunctor.map b.op ((M.endEquivalence.app (.op U)).hom p) =
      (M.endEquivalence.app (.op T)).hom (b ≫ p) :=
  (ConcreteCategory.congr_hom (M.endEquivalence.hom.naturality b.op) p).symm

theorem e34TupleValue_restriction {T U : Over S} (b : T ⟶ U)
    (p : U ⟶ M.endScheme) (i : Fin n) :
    IntegralModel.EndomorphismFamiliesId.EndomorphismFamilies.restrict A b (e34TupleValue A M U p i) = e34TupleValue A M T (b ≫ p) i := by
  apply (IntegralModel.Presentations.EndomorphismBridge.EndomorphismFamilies.e34EndomorphismEquiv A T).injective
  rw [e34_endomorphismEquiv_restrict]
  dsimp only [e34TupleValue]
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact congrFun (congrArg Subtype.val (e34Locus_restriction A M b p)) i

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.PresentationsTupleParameters
