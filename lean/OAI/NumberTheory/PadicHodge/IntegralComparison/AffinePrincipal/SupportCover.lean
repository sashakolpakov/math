import OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Diagram
import OAI.NumberTheory.PadicHodge.IntegralComparison.SectionIdealPuncturedCover

/-! # Support Cover -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.SupportCover

noncomputable section

/-! Equations for an actual section ideal give the punctured cover
on the principal coefficient category, also after pullback. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u v
variable (X : Scheme.{u}) (U : X.Opens) (hU : IsAffineOpen U)

include hU in
theorem terminal :
    X.basicOpen ((⊤_ (AlgebraicGeometry.Crystalline.Cohomology.PrincipalCoefficient.PrincipalCoefficientCategory.Object Γ(X, U))).val) = U := by
  apply le_antisymm (X.basicOpen_le _)
  have h := Diagram.monotone X U hU
    (leOfHom (Limits.terminal.from (show AlgebraicGeometry.Crystalline.Cohomology.PrincipalCoefficient.PrincipalCoefficientCategory.Object Γ(X, U) from ⟨1⟩)))
  change X.basicOpen (1 : Γ(X, U)) ≤
    X.basicOpen ((⊤_ (AlgebraicGeometry.Crystalline.Cohomology.PrincipalCoefficient.PrincipalCoefficientCategory.Object Γ(X, U))).val) at h
  simpa only [Scheme.basicOpen_one] using h

variable (Y : Scheme.{u}) (f : Y ⟶ X)

def opens : AlgebraicGeometry.Crystalline.Cohomology.PrincipalCoefficient.PrincipalCoefficientCategory.Object Γ(X, U) ⥤ Y.Opens where
  obj r := f ⁻¹ᵁ (X.basicOpen r.val)
  map h := homOfLE (fun _ hx => Diagram.monotone X U hU (leOfHom h) hx)

theorem opens_terminal : (opens X U hU Y f).obj (⊤_ _) = f ⁻¹ᵁ U := by
  change f ⁻¹ᵁ (X.basicOpen ((⊤_ (AlgebraicGeometry.Crystalline.Cohomology.PrincipalCoefficient.PrincipalCoefficientCategory.Object Γ(X, U))).val)) = _
  rw [SupportCover.terminal X U hU]

variable (I : X.IdealSheafData) {ι : Type v}
  (a : ι → Γ(X, U)) (ha : Ideal.span (Set.range a) = I.ideal ⟨U, hU⟩)

def family : ULift ι → AlgebraicGeometry.Crystalline.Cohomology.PrincipalCoefficient.PrincipalCoefficientCategory.Object Γ(X, U) := fun i => ⟨a i.down⟩

def outside : Y.Opens := f ⁻¹ᵁ (SectionIdealPuncturedCover.outside I)

include ha in
theorem below (i : ULift ι) : (opens X U hU Y f).obj (family X U a i) ≤ outside X Y f I := by
  intro y hy
  exact SectionIdealPuncturedCover.basicOpen_le I U hU a ha i.down hy

include ha in
theorem cover : (opens X U hU Y f).obj (⊤_ _) ⊓ outside X Y f I ≤
    ⨆ i, (opens X U hU Y f).obj (family X U a i) := by
  rw [opens_terminal]
  intro y hy
  have h : f y ∈ U ⊓ SectionIdealPuncturedCover.outside I := hy
  rw [SectionIdealPuncturedCover.cover I U hU a ha] at h
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp h
  exact Opens.mem_iSup.mpr ⟨⟨i⟩, hi⟩

theorem global (h : U ⊔ SectionIdealPuncturedCover.outside I = ⊤) :
    (opens X U hU Y f).obj (⊤_ _) ⊔ outside X Y f I = ⊤ := by
  rw [opens_terminal]
  apply top_unique
  intro y _
  have hy : f y ∈ U ⊔ SectionIdealPuncturedCover.outside I := by
    rw [h]
    trivial
  exact hy

variable {T : Scheme.{u}} (s : T ⟶ X) [IsClosedImmersion s]

theorem section_global (hs : ⊤ ≤ s ⁻¹ᵁ U) :
    (opens X U hU Y f).obj (⊤_ _) ⊔ outside X Y f s.ker = ⊤ :=
  global X U hU Y f s.ker (SectionIdealPuncturedCover.section_global U s hs)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.SupportCover
