import OAI.NumberTheory.PadicHodge.GeometricComparison.LargeModuleAt
import OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.ProductBaseChange
import OAI.AlgebraicGeometry.SheafCohomology.Cech.TopCatRestrict

/-! # Flasque Cech Subfamily -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FlasqueCechSubfamily

noncomputable section

/-! A flasque sheaf has exact positive Čech cohomology for an arbitrary
family of opens: restrict to its union before using cover exactness. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

universe u v w z

theorem product_iInf {C : Type u} [CompleteLattice C] {ι : Type v} (V : ι → C) :
    (∏ᶜ V) = ⨅ i, V i :=
  ((productIsProduct V).conePointUniqueUpToIso (Preorder.isLimitIInf V)).to_eq

theorem openEmbedding_preserves {X Y : TopCat.{u}} (f : X ⟶ Y)
    (hf : Topology.IsOpenEmbedding f) {ι : Type v} [Finite ι] [Nonempty ι]
    (V : ι → Opens X) : PreservesLimit (Discrete.functor V) hf.functor := by
  let : IsIso (piComparison hf.functor V) := (PartialOrder.isIso_iff_eq _).mpr (by
    rw [product_iInf, product_iInf]
    exact Topology.IsOpenEmbedding.functor_obj_iInf f hf V)
  exact PreservesProduct.of_iso_comparison _ _

variable (R : Type u) [CommRing R] (X : TopCat.{v})
  (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{max u v w} R))
  {ι : Type} (U : ι → Opens X)

abbrev union := iSup U
abbrev restrictedFamily : ι → Opens ((Opens.toTopCat X).obj (union X U)) := (Opens.map (union X U).inclusion').obj ∘ U
abbrev restrictedSheaf :=
  (AlgebraicGeometry.SheafCohomology.Cech.TopCatRestrict.TopCat.Sheaf.restrict (ModuleCat.{max u v w} R) (union X U).isOpenEmbedding).obj F

theorem cover : iSup (restrictedFamily X U) = ⊤ := by
  erw [restrictedFamily, ← Opens.map_iSup]
  apply Opens.ext
  ext x
  exact iff_true_intro x.property

theorem image_family : (union X U).isOpenEmbedding.functor.obj ∘ restrictedFamily X U = U := by
  funext i
  exact (Opens.functor_map_eq_inf (union X U) (U i)).trans (inf_eq_left.mpr (le_iSup U i))

def complexIso :
    (NonemptyCechNerve.complexFunctor (restrictedFamily X U)).obj (restrictedSheaf R X F U).obj ≅
      (NonemptyCechNerve.complexFunctor U).obj F.obj := by
  let : ∀ (n : ℕ) (t : Fin (n + 1) → ι),
      PreservesLimit (Discrete.functor (restrictedFamily X U ∘ t)) (union X U).isOpenEmbedding.functor :=
    fun n t => openEmbedding_preserves (union X U).inclusion' (union X U).isOpenEmbedding _
  exact GeometricComparison.NonemptyCech.ProductBaseChange.NonemptyCechProductBaseChange.complexIso
    (union X U).isOpenEmbedding.functor (restrictedFamily X U) F.obj ≪≫
      eqToIso (congrArg (fun V => (NonemptyCechNerve.complexFunctor V).obj F.obj) (image_family X U))

theorem exactAt_succ [TopCat.Presheaf.IsFlasque (X := X) F.obj] (n : ℕ) :
    ((NonemptyCechNerve.complexFunctor U).obj F.obj).ExactAt (n + 1) := by
  let : TopCat.Sheaf.IsFlasque (restrictedSheaf R X F U) :=
    AlgebraicGeometry.SheafCohomology.Cech.TopCatRestrict.TopCat.Sheaf.IsFlasque.of_restrict (ModuleCat.{max u v w} R) F (union X U).isOpenEmbedding
  have h := GeometricComparison.LargeModuleAt.LargeModuleFlasqueCech.exactAt_succ R ((Opens.toTopCat X).obj (union X U))
    (restrictedSheaf R X F U) (restrictedFamily X U) (cover X U) n
  exact h.of_iso (complexIso R X F U)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FlasqueCechSubfamily
