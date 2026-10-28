import OAI.AlgebraicGeometry.Quotients.FiniteDescent.RationalSheafIs
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.SubmoduleSheafIs

/-! # Fractional Ideal Is -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.FractionalIdealIs.Construction.FractionalIdealSheaf

noncomputable section

/-! Sheaves of rational functions satisfying prescribed stalkwise fractional-ideal bounds. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

variable {X : Scheme.{u}} [IsIntegral X]
variable (F : ∀ x : X, Submodule (X.presheaf.stalk x) X.functionField)

def module (U : X.Opens) : Submodule Γ(X, U) (RationalSheafIs.Construction.RationalSheaf.sections U) where
  carrier := {s | ∀ x : U, s ⟨⟨x⟩⟩ ∈ F x}
  zero_mem' x := (F x).zero_mem
  add_mem' hs ht x := (F x).add_mem (hs x) (ht x)
  smul_mem' a s hs x := by
    have hm := (F x).smul_mem (X.presheaf.germ U x x.2 a) (hs x)
    have : Nonempty U := ⟨x⟩
    change algebraMap (X.presheaf.stalk x) X.functionField
      (X.presheaf.germ U x x.2 a) * s ⟨⟨x⟩⟩ ∈ F x at hm
    rw [X.algebraMap_germ_eq_germToFunctionField] at hm
    exact hm

theorem mem_module (U : X.Opens) (s : RationalSheafIs.Construction.RationalSheaf.sections U) :
    s ∈ module F U ↔ ∀ x : U, s ⟨⟨x⟩⟩ ∈ F x := Iff.rfl

def submodule : (RationalSheafIs.Construction.RationalSheaf.sheaf (X := X)).val.Submodule where
  obj U := module F U.unop
  map {U V} h := by
    intro s hs
    change ∀ x : V.unop, RationalSheafIs.Construction.RationalSheaf.restrict h.unop.le s ⟨⟨x⟩⟩ ∈ F x
    intro x
    exact hs ⟨x, h.unop.le x.2⟩

theorem isLocal : SubmoduleSheafIs.Construction.SubmoduleSheaf.IsLocal RationalSheafIs.Construction.RationalSheaf.sheaf (submodule F) := by
  intro ι U s hs
  change ∀ x : (iSup U : X.Opens), s ⟨⟨x⟩⟩ ∈ F x
  intro x
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp x.2
  exact hs i ⟨x, hi⟩

def sheaf : X.Modules :=
  SubmoduleSheafIs.Construction.SubmoduleSheaf.ofLocal RationalSheafIs.Construction.RationalSheaf.sheaf (submodule F) (isLocal F)

def inclusion : sheaf F ⟶ RationalSheafIs.Construction.RationalSheaf.sheaf :=
  SubmoduleSheafIs.Construction.SubmoduleSheaf.inclusion RationalSheafIs.Construction.RationalSheaf.sheaf (submodule F) (isLocal F)

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.FractionalIdealIs.Construction.FractionalIdealSheaf
