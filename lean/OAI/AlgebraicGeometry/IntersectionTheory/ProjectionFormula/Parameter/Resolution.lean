import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.ScalarQuotient
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.QuasiIso
import Mathlib.RingTheory.Flat.TorsionFree

/-! # Resolution -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.Resolution

noncomputable section

/-! A projective resolution descends to the parameter quotient ring
when the parameter is regular both on the ring and on the resolved
module. The quasi-isomorphism is proved using the homology sequence. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.ScalarQuotient

variable (R : Type u) [CommRing R] (r : R)

theorem quotient_quasiIso {K L : ChainComplex (ModuleCat.{u} R) ℕ} (φ : K ⟶ L)
    (hK : ∀ i, IsSMulRegular (K.X i) r)
    (hL : ∀ i, IsSMulRegular (L.X i) r) [QuasiIso φ] :
    QuasiIso (((ScalarQuotient.quotient R r).mapHomologicalComplex (ComplexShape.down ℕ)).map φ) := by
  apply (HomologicalComplex.quasiIso_map_iff_of_preservesHomology _
    (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {r})))).mp
  change QuasiIso
    (((QuotientComplex.quotient R r).mapHomologicalComplex (ComplexShape.down ℕ)).map φ)
  exact Parameter.QuasiIso.quasiIso R r φ hK hL

theorem projective_regular (hregular : IsSMulRegular R r) (M : ModuleCat.{u} R)
    [Projective M] : IsSMulRegular M r := by
  let : Module.Projective R M := inferInstance
  let : Module.Flat R M := inferInstance
  apply Module.Flat.isSMulRegular_of_isRegular
  exact (Commute.isRegular_iff (fun b => Commute.all r b)).mpr hregular

theorem single_regular (M : ModuleCat.{u} R) (hM : IsSMulRegular M r) (i : ℕ) :
    IsSMulRegular (((ChainComplex.single₀ (ModuleCat R)).obj M).X i) r := by
  cases i with
  | zero => exact hM
  | succ i =>
    let : Subsingleton (((ChainComplex.single₀ (ModuleCat R)).obj M).X (i + 1)) :=
      ModuleCat.subsingleton_of_isZero
        (HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega))
    exact fun _ _ _ => Subsingleton.elim _ _

def resolution (hregular : IsSMulRegular R r) (M : ModuleCat.{u} R)
    (hM : IsSMulRegular M r) (P : ProjectiveResolution M) :
    ProjectiveResolution ((ScalarQuotient.quotient R r).obj M) where
  complex := ((ScalarQuotient.quotient R r).mapHomologicalComplex _).obj P.complex
  projective n := by
    change Projective ((ScalarQuotient.quotient R r).obj (P.complex.X n))
    exact Functor.PreservesProjectiveObjects.projective_obj (P.projective n)
  π := ((ScalarQuotient.quotient R r).mapHomologicalComplex _).map P.π ≫
    (HomologicalComplex.singleMapHomologicalComplex _ _ _).hom.app _
  quasiIso := by
    let : QuasiIso (((ScalarQuotient.quotient R r).mapHomologicalComplex _).map P.π) :=
      quotient_quasiIso R r P.π
        (fun i => projective_regular R r hregular (P.complex.X i))
        (single_regular R r M hM)
    infer_instance

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.Resolution
