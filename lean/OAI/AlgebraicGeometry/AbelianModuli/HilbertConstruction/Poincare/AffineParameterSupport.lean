import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PoincareStalk.FieldSupport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ParameterVanishingIdeal
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.FlatCochainSupport

/-! # Affine Parameter Support -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Over any affine parameter scheme, the genuine Poincare cohomology model is supported on the inverse image of the dual zero section. Its coefficient ideal is defined from that actual geometric subset. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S T : Scheme.{u}} [IsAffine T] {g : ℕ} {A : Abelian.Schemes.AbelianScheme g S}
variable (D : Dual.Data.DualAbelianData A) (t : T ⟶ D.abelian.scheme.left)

def Dual.Data.DualAbelianData.poincareAffineParameterIdeal : Ideal Γ(T, ⊤) :=
  Affine.ParameterVanishingIdeal.affineParameterVanishingIdeal (t ⁻¹' Set.range η[D.abelian.scheme].left)

variable {P : Scheme.{u}} [P.IsSeparated]
variable {a : P ⟶ (D.abelian.scheme ⊗ A.scheme).left} {b : P ⟶ T}
variable (H : IsPullback a b (pullback.fst D.abelian.scheme.hom A.scheme.hom) t)
variable {κ : Type u} [LinearOrder κ] [Finite κ] (U : κ → P.Opens)
variable (hU : iSup U = ⊤) (ha : ∀ i, IsAffineOpen (U i))
variable (he : ∀ i, Nonempty ((Scheme.Modules.pullback (U i).ι).obj
  (D.poincare.pullback a).sheaf ≅ Line.Bundles.structureModule (U i).toScheme))
variable {C : CochainComplex (ModuleCat.{u} Γ(T, ⊤)) ℕ}
variable (φ : C ⟶ Ordered.CoefficientCechComplex.orderedCoefficientCechComplex b.appTop.hom (D.poincare.pullback a).sheaf U)
variable (ht : ∀ (B : Type u) [AddCommGroup B] [Module Γ(T, ⊤) B], QuasiIso (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map B φ))

include H hU ha he ht in
theorem Dual.Data.DualAbelianData.poincareAffine_model_field_support : Cochain.FieldSupport.CochainFieldSupport C (D.poincareAffineParameterIdeal t) := by
  intro B _ _ hnot
  let R := Γ(T, ⊤)
  let j : Spec (.of B) ⟶ T := Affine.QuotientCoefficientMap.affineCoordinateMap (algebraMap R B)
  let a' := pullback.fst b j
  let b' := pullback.snd b j
  let H' : IsPullback a' b' b j := IsPullback.of_hasPullback b j
  let c : Spec (.of B) ⟶ S := (j ≫ t) ≫ D.abelian.scheme.hom
  let x : (Over.map c).obj (𝟙_ (Over (Spec (.of B)))) ⟶ D.abelian.scheme :=
    Over.homMk (j ≫ t) (by change _ = (𝟙 _) ≫ c; exact (Category.id_comp c).symm)
  have hout : t (j (IsLocalRing.closedPoint B)) ∉ Set.range η[D.abelian.scheme].left := by
    intro hz
    exact hnot (Affine.ParameterVanishingIdeal.affineParameterVanishingIdeal_le_kernel_of_point_mem
      (t ⁻¹' Set.range η[D.abelian.scheme].left) (algebraMap R B) hz)
  have hx : x ≠ 1 :=
    D.fieldDualPoint_ne_one_of_point_outside_zero c x (IsLocalRing.closedPoint B) hout
  let HF : IsPullback (a' ≫ a) b' (pullback.fst D.abelian.scheme.hom A.scheme.hom) x.left :=
    H'.paste_horiz H
  let L := D.poincare.pullback a
  let e : (L.pullback a').sheaf ≅ (D.poincare.pullback (a' ≫ a)).sheaf :=
    (Scheme.Modules.pullbackComp a' a).app D.poincare.sheaf
  have hAlg : (HilbertConstruction.Spec.CoefficientCechComparison.specBaseCoefficientMap j).toAlgebra = (inferInstance : Algebra R B) := by
    rw [Affine.QuotientCoefficientMap.specBaseCoefficientMap_affineCoordinateMap]
    exact toAlgebra_algebraMap
  intro q
  have hzero := D.poincareFieldFiber_cohomology_vanish c x HF hx q
  let eH := (Zariski.Cohomology.ZariskiCohomology.zariskiFunctor (CategoryTheory.Limits.pullback b j) q).mapIso e
  have hi : Function.Injective eH.hom := (AddCommGrpCat.mono_iff_injective eH.hom).mp inferInstance
  have hL : Subsingleton (Zariski.Cohomology.ZariskiCohomology.H (L.pullback a').sheaf q) :=
    ⟨fun y z => hi (hzero.elim _ _)⟩
  have hres := HilbertConstruction.Spec.ModelAllDegreeVanishing.spec_model_exactAt_of_cohomology_zero_all H' L U hU ha he φ ht q hL
  have hexa : (((HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R B).mapHomologicalComplex (.up ℕ)).obj C).ExactAt q := by
    erw [hAlg] at hres
    exact hres
  exact (Base.ChangeTensorExactness.baseChange_exactAt_iff_tensor C q).mp hexa

include H hU ha he ht in
theorem Dual.Data.DualAbelianData.poincareAffine_model_homology_support
    (hfin : ∀ q, Module.Finite Γ(T, ⊤) (C.X q))
    (hflat : ∀ q, Module.Flat Γ(T, ⊤) (C.X q)) (q : ℕ) :
    Module.support Γ(T, ⊤) (C.homology q) ⊆
      PrimeSpectrum.zeroLocus (D.poincareAffineParameterIdeal t : Set Γ(T, ⊤)) :=
  HilbertConstruction.Finite.FlatCochainSupport.finiteFlatCochain_fieldSupport_homology_support C hfin hflat (D.poincareAffineParameterIdeal t)
    (D.poincareAffine_model_field_support t H U hU ha he φ ht) q

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
