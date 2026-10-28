import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Basic.Complex.Basic

/-! # Disjoint Sheaf Sections -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.DisjointSheafSections

noncomputable section

/-! Actual sheaf sections split over a disjoint open cover, including an empty cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

variable {M : TopCat.{0}} (F : TopCat.Sheaf (ModuleCat.{0} ℂ) M)
  {ι : Type} (U : ι → Opens M) (V : Opens M) (iUV : ∀ i, U i ⟶ V)

def sectionRestriction : F.obj.obj (op V) →ₗ[ℂ] (∀ i, F.obj.obj (op (U i))) :=
  LinearMap.pi fun i => (F.obj.map (iUV i).op).hom

theorem sectionRestriction_injective (hcover : V ≤ iSup U) :
    Function.Injective (sectionRestriction F U V iUV) := by
  intro x y h
  apply F.eq_of_locally_eq' U V iUV hcover
  intro i
  exact congrFun h i

theorem disjoint_sections_compatible (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (s : ∀ i, F.obj.obj (op (U i))) : TopCat.Presheaf.IsCompatible F.obj U s := by
  intro i j
  by_cases hij : i = j
  · subst j
    rfl
  · have hempty : U i ⊓ U j = ⊥ := (hdisj hij).eq_bot
    have : Subsingleton (F.obj.obj (op (U i ⊓ U j))) :=
      ModuleCat.isZero_iff_subsingleton.mp (F.isTerminalOfEqEmpty hempty).isZero
    exact Subsingleton.elim _ _

theorem sectionRestriction_surjective (hcover : V ≤ iSup U)
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j))) :
    Function.Surjective (sectionRestriction F U V iUV) := by
  intro s
  obtain ⟨x, hx, _⟩ := F.existsUnique_gluing' U V iUV hcover s (disjoint_sections_compatible F U hdisj s)
  exact ⟨x, funext hx⟩

def sectionEquiv (hcover : V ≤ iSup U)
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j))) :
    F.obj.obj (op V) ≃ₗ[ℂ] (∀ i, F.obj.obj (op (U i))) :=
  LinearEquiv.ofBijective (sectionRestriction F U V iUV)
    ⟨sectionRestriction_injective F U V iUV hcover, sectionRestriction_surjective F U V iUV hcover hdisj⟩

theorem sectionEquiv_apply (hcover : V ≤ iSup U)
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j))) (x : F.obj.obj (op V)) (i : ι) :
    sectionEquiv F U V iUV hcover hdisj x i = F.obj.map (iUV i).op x := rfl

theorem sectionEquiv_naturality {G : TopCat.Sheaf (ModuleCat.{0} ℂ) M} (φ : F ⟶ G)
    (hcover : V ≤ iSup U) (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (x : F.obj.obj (op V)) (i : ι) :
    sectionEquiv G U V iUV hcover hdisj (φ.hom.app (op V) x) i =
      φ.hom.app (op (U i)) (sectionEquiv F U V iUV hcover hdisj x i) := by
  exact (ConcreteCategory.congr_hom (φ.hom.naturality (iUV i).op) x).symm

end

end OAI.AlgebraicGeometry.Comparison.Betti.DisjointSheafSections
