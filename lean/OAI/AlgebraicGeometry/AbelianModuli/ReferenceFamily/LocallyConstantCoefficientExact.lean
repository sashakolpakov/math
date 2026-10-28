import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntegerSingularSheafComparison
import OAI.AlgebraicGeometry.DivisorClass.Chern.Abelian.SheafLocalExact

/-! # Locally Constant Coefficient Exact -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LocallyConstantCoefficientExact

noncomputable section

/-! Short exact coefficient sequences give actual sectionwise exact
sequences of locally constant abelian sheaves. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

open OAI.AlgebraicGeometry.DivisorClass.Chern.Abelian.SheafLocalExact

variable {M N P : ModuleCat.{0} ℤ} (f : M ⟶ N) (g : N ⟶ P) (X : TopCat.{0})

def integerLocallyConstantSheafMap :
    IntegerSingularSheafComparison.integerLocallyConstantAbelianSheaf M X ⟶ IntegerSingularSheafComparison.integerLocallyConstantAbelianSheaf N X :=
  (IntegerSingularSheafComparison.integerCoefficientSheafForget X).map (LocallyConstantModuleSheaf.coefficientLocallyConstantSheafMap M X f)

theorem integerLocallyConstantSheafMap_injective (hf : Function.Injective f) (U : Opens X) :
    Function.Injective ((integerLocallyConstantSheafMap f X).hom.app (op U)) := by
  intro a b hab
  apply LocallyConstant.ext
  intro x
  apply hf
  exact congrArg (fun c : LocallyConstant U N => c x) hab

theorem integerLocallyConstantSheafMap_surjective (hf : Function.Surjective f) (U : Opens X) :
    Function.Surjective ((integerLocallyConstantSheafMap f X).hom.app (op U)) := by
  intro b
  change LocallyConstant U N at b
  let t : N → M := fun y => (hf y).choose
  refine ⟨⟨fun x => t (b x), b.isLocallyConstant.comp t⟩, ?_⟩
  apply LocallyConstant.ext
  intro x
  exact (hf (b x)).choose_spec

theorem integerLocallyConstantSheafMap_mono (hf : Function.Injective f) :
    Mono (integerLocallyConstantSheafMap f X) := by
  apply (CategoryTheory.Sheaf.Hom.mono_iff_presheaf_mono _ _ _).mpr
  apply (NatTrans.mono_iff_mono_app _).mpr
  intro U
  exact (AddCommGrpCat.mono_iff_injective _).mpr (integerLocallyConstantSheafMap_injective f X hf U.unop)

theorem integerLocallyConstantSheafMap_epi (hf : Function.Surjective f) :
    Epi (integerLocallyConstantSheafMap f X) := by
  have : ∀ U, Epi ((integerLocallyConstantSheafMap f X).hom.app U) := fun U =>
    (AddCommGrpCat.epi_iff_surjective _).mpr (integerLocallyConstantSheafMap_surjective f X hf U.unop)
  have : Epi (integerLocallyConstantSheafMap f X).hom := NatTrans.epi_of_epi_app _
  exact CategoryTheory.Sheaf.Hom.epi_of_presheaf_epi (Opens.grothendieckTopology X)
    AddCommGrpCat.{0} (integerLocallyConstantSheafMap f X)

theorem integerLocallyConstantSheafMap_comp_zero (hz : ∀ a : M, g (f a) = 0) :
    integerLocallyConstantSheafMap f X ≫ integerLocallyConstantSheafMap g X = 0 := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro a
  change LocallyConstant U.unop M at a
  apply LocallyConstant.ext
  intro x
  exact hz (a x)

def locallyConstantCoefficientSequence (hz : ∀ a : M, g (f a) = 0) :
    ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X) :=
  ShortComplex.mk (integerLocallyConstantSheafMap f X) (integerLocallyConstantSheafMap g X)
    (integerLocallyConstantSheafMap_comp_zero f g X hz)

theorem locallyConstantCoefficientSequence_exact (hz : ∀ a : M, g (f a) = 0)
    (he : ∀ b : N, g b = 0 → ∃ a : M, f a = b) :
    (locallyConstantCoefficientSequence f g X hz).Exact := by
  classical
  apply DivisorClass.Chern.Abelian.SheafLocalExact.abelianSheaf_exact_of_section_exact X
  intro U
  apply (ShortComplex.ab_exact_iff _).mpr
  intro b hb
  change LocallyConstant U N at b
  let t : N → M := Function.invFun f
  refine ⟨⟨fun x => t (b x), b.isLocallyConstant.comp t⟩, ?_⟩
  apply LocallyConstant.ext
  intro x
  have hb' : g (b x) = 0 := congrArg (fun c : LocallyConstant U P => c x) hb
  obtain ⟨a, ha⟩ := he (b x) hb'
  change f (Function.invFun f (b x)) = b x
  rw [← ha]
  exact Function.apply_invFun_apply

theorem locallyConstantCoefficientSequence_shortExact (hz : ∀ a : M, g (f a) = 0)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (he : ∀ b : N, g b = 0 → ∃ a : M, f a = b) :
    (locallyConstantCoefficientSequence f g X hz).ShortExact where
  exact := locallyConstantCoefficientSequence_exact f g X hz he
  mono_f := integerLocallyConstantSheafMap_mono f X hf
  epi_g := integerLocallyConstantSheafMap_epi g X hg

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LocallyConstantCoefficientExact
