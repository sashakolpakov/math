import OAI.AlgebraicGeometry.Quotients.FiniteDescent.SubmoduleSheafIs

/-! # Stalk Ideal Is -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.StalkIdealIs.Construction.StalkIdealSheaf

noncomputable section

/-! The subsheaf of regular functions whose germs belong to prescribed stalk ideals. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

variable {X : Scheme.{u}} (I : ∀ x : X, Ideal (X.presheaf.stalk x))

def ideal (U : X.Opens) : Ideal Γ(X, U) :=
  ⨅ x : U, (I x).comap (X.presheaf.germ U x x.2).hom

theorem mem_ideal (U : X.Opens) (s : Γ(X, U)) :
    s ∈ ideal I U ↔ ∀ x : U, X.presheaf.germ U x x.2 s ∈ I x := by
  simp only [ideal, Ideal.mem_iInf, Ideal.mem_comap]

def submodule : (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X).val.Submodule where
  obj U := ideal I U.unop
  map {U V} h := by
    intro s hs
    change Γ(X, U.unop) at s
    change X.presheaf.map h s ∈ ideal I V.unop
    apply (mem_ideal I V.unop _).mpr
    intro x
    exact (X.presheaf.germ_res_apply h.unop x x.2 s).symm ▸
      (mem_ideal I U.unop s).mp hs ⟨x, h.unop.le x.2⟩

theorem isLocal : SubmoduleSheafIs.Construction.SubmoduleSheaf.IsLocal (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) (submodule I) := by
  intro ι U s hs
  change Γ(X, iSup U) at s
  apply (mem_ideal I (iSup U) s).mpr
  intro x
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp x.2
  have h := (mem_ideal I (U i) _).mp (hs i) ⟨x, hi⟩
  change X.presheaf.germ (U i) x hi (X.presheaf.map (Opens.leSupr U i).op s) ∈ I x at h
  rw [X.presheaf.germ_res_apply (Opens.leSupr U i) x hi s] at h
  exact h

def sheaf : X.Modules :=
  SubmoduleSheafIs.Construction.SubmoduleSheaf.ofLocal (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) (submodule I) (isLocal I)

def inclusion : sheaf I ⟶ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X :=
  SubmoduleSheafIs.Construction.SubmoduleSheaf.inclusion (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) (submodule I) (isLocal I)

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.StalkIdealIs.Construction.StalkIdealSheaf
