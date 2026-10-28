import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TopologicalSheafRestriction
import Mathlib.Algebra.Homology.ShortComplex.Ab

/-! # Two Open Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.TwoOpenSections.IntrinsicCech

noncomputable section

/-! The actual section sequence for two open subsets is left exact. It is short exact for flasque sheaves. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
universe u
variable {X : TopCat.{u}} (F : TopCat.Sheaf AddCommGrpCat.{u} X) (U V : Opens X)

def twoOpenSectionsRestriction : F.obj.obj (op (U ⊔ V)) →+
    (F.obj.obj (op U) × F.obj.obj (op V)) :=
  (F.obj.map (homOfLE le_sup_left).op).hom.prod
    (F.obj.map (homOfLE le_sup_right).op).hom

def twoOpenSectionsDifference : (F.obj.obj (op U) × F.obj.obj (op V)) →+
    F.obj.obj (op (U ⊓ V)) :=
  ((F.obj.map (homOfLE inf_le_left).op).hom.comp (AddMonoidHom.fst _ _)) -
    ((F.obj.map (homOfLE inf_le_right).op).hom.comp (AddMonoidHom.snd _ _))

theorem twoOpenSectionsRestriction_naturality
    {G : TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (x : F.obj.obj (op (U ⊔ V))) :
    twoOpenSectionsRestriction G U V (f.hom.app (op (U ⊔ V)) x) =
      (f.hom.app (op U) (twoOpenSectionsRestriction F U V x).1,
        f.hom.app (op V) (twoOpenSectionsRestriction F U V x).2) := by
  apply Prod.ext
  · exact (ConcreteCategory.congr_hom (f.hom.naturality (homOfLE le_sup_left).op) x).symm
  · exact (ConcreteCategory.congr_hom (f.hom.naturality (homOfLE le_sup_right).op) x).symm

theorem twoOpenSectionsDifference_naturality
    {G : TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (x : F.obj.obj (op U) × F.obj.obj (op V)) :
    f.hom.app (op (U ⊓ V)) (twoOpenSectionsDifference F U V x) =
      twoOpenSectionsDifference G U V (f.hom.app (op U) x.1, f.hom.app (op V) x.2) := by
  change f.hom.app (op (U ⊓ V))
      (F.obj.map (homOfLE inf_le_left).op x.1 - F.obj.map (homOfLE inf_le_right).op x.2) =
    G.obj.map (homOfLE inf_le_left).op (f.hom.app (op U) x.1) -
      G.obj.map (homOfLE inf_le_right).op (f.hom.app (op V) x.2)
  rw [map_sub]
  exact congrArg₂ (fun a b => a - b)
    (ConcreteCategory.congr_hom (f.hom.naturality (homOfLE inf_le_left).op) x.1)
    (ConcreteCategory.congr_hom (f.hom.naturality (homOfLE inf_le_right).op) x.2)

theorem twoOpenSections_comp (x : F.obj.obj (op (U ⊔ V))) :
    twoOpenSectionsDifference F U V (twoOpenSectionsRestriction F U V x) = 0 := by
  change F.obj.map (homOfLE inf_le_left).op
      (F.obj.map (homOfLE le_sup_left).op x) -
    F.obj.map (homOfLE inf_le_right).op
      (F.obj.map (homOfLE le_sup_right).op x) = 0
  rw [sub_eq_zero]
  simp only [← ConcreteCategory.comp_apply, ← F.obj.map_comp]
  exact congrArg (fun k => F.obj.map k x) (Subsingleton.elim _ _)

def twoOpenSectionsShortComplex : ShortComplex AddCommGrpCat.{u} :=
  ShortComplex.mk (AddCommGrpCat.ofHom (twoOpenSectionsRestriction F U V))
    (AddCommGrpCat.ofHom (twoOpenSectionsDifference F U V)) (by
      ext x
      exact twoOpenSections_comp F U V x)

theorem twoOpenSectionsRestriction_injective : Function.Injective (twoOpenSectionsRestriction F U V) := by
  intro x y hxy
  have hu := congrArg Prod.fst hxy
  have hv := congrArg Prod.snd hxy
  apply TopCat.Presheaf.IsSheaf.section_ext F.property
  intro z hz
  rcases hz with hz | hz
  · exact ⟨U, le_sup_left, hz, hu⟩
  · exact ⟨V, le_sup_right, hz, hv⟩

theorem twoOpenSections_exact : (twoOpenSectionsShortComplex F U V).Exact := by
  rw [ShortComplex.ab_exact_iff]
  rintro ⟨x, y⟩ hxy
  have h : F.obj.map (homOfLE inf_le_left).op x =
      F.obj.map (homOfLE inf_le_right).op y := sub_eq_zero.mp hxy
  have h' : F.obj.map (homOfLE (show V ⊓ U ≤ V from inf_le_left)).op y =
      F.obj.map (homOfLE (show V ⊓ U ≤ U from inf_le_right)).op x := by
    have hh := congrArg (F.obj.map (homOfLE (show V ⊓ U ≤ U ⊓ V by rw [inf_comm])).op) h
    have hleft : F.obj.map (homOfLE (show V ⊓ U ≤ U ⊓ V by rw [inf_comm])).op
        (F.obj.map (homOfLE inf_le_right).op y) =
        F.obj.map (homOfLE (show V ⊓ U ≤ V from inf_le_left)).op y := by
      rw [← ConcreteCategory.comp_apply, ← F.obj.map_comp]
      exact congrArg (fun k => F.obj.map k y) (Subsingleton.elim _ _)
    have hright : F.obj.map (homOfLE (show V ⊓ U ≤ U ⊓ V by rw [inf_comm])).op
        (F.obj.map (homOfLE inf_le_left).op x) =
        F.obj.map (homOfLE (show V ⊓ U ≤ U from inf_le_right)).op x := by
      rw [← ConcreteCategory.comp_apply, ← F.obj.map_comp]
      exact congrArg (fun k => F.obj.map k x) (Subsingleton.elim _ _)
    exact hleft.symm.trans (hh.symm.trans hright)
  let W : Fin 2 → Opens X := ![U, V]
  let sf : (i : Fin 2) → F.obj.obj (op (W i))
    | 0 => x
    | 1 => y
  have hcomp : TopCat.Presheaf.IsCompatible F.obj W sf := by
    intro i j
    fin_cases i <;> fin_cases j
    · rfl
    · exact h
    · exact h'
    · rfl
  let inclusions (i : Fin 2) : W i ⟶ U ⊔ V :=
    homOfLE (by
      fin_cases i
      · exact le_sup_left
      · exact le_sup_right)
  obtain ⟨z, hz, _⟩ := F.existsUnique_gluing' W (U ⊔ V) inclusions
    (sup_le (le_iSup W (0 : Fin 2)) (le_iSup W (1 : Fin 2))) sf hcomp
  exact ⟨z, Prod.ext (hz 0) (hz 1)⟩

theorem twoOpenSectionsDifference_surjective [F.IsFlasque] :
    Function.Surjective (twoOpenSectionsDifference F U V) := by
  intro z
  obtain ⟨x, hx⟩ := (AddCommGrpCat.epi_iff_surjective
    (F.obj.map (homOfLE (show U ⊓ V ≤ U from inf_le_left)).op)).mp inferInstance z
  refine ⟨(x, 0), ?_⟩
  change F.obj.map (homOfLE inf_le_left).op x - F.obj.map (homOfLE inf_le_right).op 0 = z
  rw [map_zero, sub_zero]
  exact hx

theorem twoOpenSections_shortExact [F.IsFlasque] : (twoOpenSectionsShortComplex F U V).ShortExact := by
  have : Mono (twoOpenSectionsShortComplex F U V).f :=
    (AddCommGrpCat.mono_iff_injective _).mpr (twoOpenSectionsRestriction_injective F U V)
  have : Epi (twoOpenSectionsShortComplex F U V).g :=
    (AddCommGrpCat.epi_iff_surjective _).mpr (twoOpenSectionsDifference_surjective F U V)
  exact { exact := twoOpenSections_exact F U V }

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.TwoOpenSections.IntrinsicCech
