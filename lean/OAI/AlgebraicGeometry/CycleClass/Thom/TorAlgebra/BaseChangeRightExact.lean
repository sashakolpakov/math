import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.FlatExtension
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # Base Change Right Exact -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.BaseChangeRightExact

noncomputable section

/-! The actual extension-of-scalars functor is right exact for every
algebra. This does not require the algebra itself to be flat. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open scoped TensorProduct

open OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.FlatExtension

set_option backward.isDefEq.respectTransparency false

universe u
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

theorem map_exact_of_epi (K : ShortComplex (ModuleCat.{u} R)) (hK : K.Exact) [Epi K.g] :
    (K.map (FlatExtension.baseChange R S)).Exact := by
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hK ⊢
  exact lTensor_exact S hK ((ModuleCat.epi_iff_surjective K.g).mp inferInstance)

instance baseChange_preservesFiniteColimits : PreservesFiniteColimits (FlatExtension.baseChange R S) := by
  apply (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi (FlatExtension.baseChange R S)).mpr
  intro K hK
  let : Epi K.g := hK.epi_g
  refine ⟨map_exact_of_epi R S K hK.exact, ?_⟩
  apply (ModuleCat.epi_iff_surjective ((FlatExtension.baseChange R S).map K.g)).mpr
  exact LinearMap.lTensor_surjective S hK.moduleCat_surjective_g

theorem tensor_algebraMap_smul (M : ModuleCat.{u} R) (r : R) (t : S ⊗[R] M) :
    (algebraMap R S r) • t = r • t :=
  IsScalarTower.algebraMap_smul S r t

def restrictBaseChangeComponent (M : ModuleCat.{u} R) :
    (ModuleCat.restrictScalars (algebraMap R S)).obj ((FlatExtension.baseChange R S).obj M) ≃ₗ[R]
      (tensorLeft (ModuleCat.of R S)).obj M where
  __ := AddEquiv.refl (S ⊗[R] M)
  map_smul' r t := tensor_algebraMap_smul R S M r t

/-- On underlying R-modules, the actual scalar extension is the
ordinary tensor-left functor used to define native Tor. -/
def restrictBaseChangeIso :
    FlatExtension.baseChange R S ⋙ ModuleCat.restrictScalars (algebraMap R S) ≅
      tensorLeft (ModuleCat.of R S) :=
  NatIso.ofComponents (fun M => (restrictBaseChangeComponent R S M).toModuleIso)
    (by
      intro M M' f
      ext t
      rfl)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.BaseChangeRightExact
