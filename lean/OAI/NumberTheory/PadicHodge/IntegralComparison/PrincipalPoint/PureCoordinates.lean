import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalPoint.SingleCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalReference.Concentration

/-! # Pure Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalPoint.PureCoordinates

noncomputable section

/-! The actual local survivor map has the same ordinary coefficient
coordinates as the original single-sheaf recovery map. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y T S : Scheme.{u}} [X.IsSeparated] [Y.IsSeparated]
  (π : Y ⟶ S) (i : X ⟶ Y) [IsClosedImmersion i] (s₀ : T ⟶ X) [IsClosedImmersion s₀]
  (U : Y.Opens) (hU : IsAffineOpen U) (hcontains : ⊤ ≤ (s₀ ≫ i) ⁻¹ᵁ U)
  {a g : ℕ} (s : Fin a → Γ(Y,U)) (t : Fin g → Γ(Y,U))
  (hs : Ideal.span (Set.range s) = i.ker.ideal ⟨U,hU⟩)
  (hst : Ideal.span (Set.range (Fin.append s t)) = (s₀ ≫ i).ker.ideal ⟨U,hU⟩)
  {κ : Type u} [LinearOrder κ] (V : κ → Y.Opens) (hV : iSup V = ⊤)
  (haV : ∀ j, IsAffineOpen (V j))
  (K : CochainComplex Y.Modules ℕ) [∀ q, (K.X q).IsQuasicoherent]
  (c : ℕ) (hK : ∀ q, q ≠ c → K.ExactAt q)
  (N : X.Modules) [N.IsQuasicoherent]
  (e : K.homology c ≅ (Scheme.Modules.pushforward i).obj N)
  (q : ℕ) (hq : q=g+c)

abbrev family := Fraction.family U t
abbrev principal := Principal.ModuleFunctor.functor U hU
abbrev supported := Supported.CechHomotopyEquivalence.functor (R := Γ(Y,U)) (family U t) q
abbrev coefficient := (Scheme.Modules.pushforward i).obj N

def localPure :=
  (PrincipalReference.Concentration.Reference.iso U hU (family U t) K c hK q).hom ≫
    (PrincipalReference.Concentration.Reference.functor U hU (family U t) q).map
      ((single Y.Modules (.up ℕ) c).map e.hom)

def localMap := localPure i U hU t K c hK N e q ≫
  (supported U t q).map
    ((singleMapHomologicalComplex (principal U hU) (.up ℕ) c).hom.app (coefficient i N))

omit [X.IsSeparated] [Y.IsSeparated] [IsClosedImmersion i] [N.IsQuasicoherent] in
theorem localMap_eq : localMap i U hU t K c hK N e q =
    (PrincipalReference.Concentration.Reference.iso U hU (family U t) K c hK q).hom ≫
      (supported U t q).map
        ((singleMapHomologicalComplex (principal U hU) (.up ℕ) c).hom.app (K.homology c)) ≫
      (supported U t q).map
        ((single _ (.up ℕ) c).map ((principal U hU).map e.hom)) := by
  have h := congrArg (fun f => (supported U t q).map f)
    ((singleMapHomologicalComplex (principal U hU) (.up ℕ) c).hom.naturality e.hom)
  simp only [Functor.map_comp] at h
  dsimp only [localMap, localPure]
  simp only [Category.assoc]
  exact congrArg
    (fun f => (PrincipalReference.Concentration.Reference.iso U hU (family U t) K c hK q).hom ≫ f) h

theorem coordinates :
    (Principal.AdditiveSections.forgetScalars U).map (localMap i U hU t K c hK N e q) ≫
      (Principal.AdditiveSections.forgetScalars U).map
        (Principal.SingleModuleCoordinates.moduleCoordinates U hU (coefficient i N) c
          (family U t) g q hq).hom ≫
      SingleCoordinates.coefficientComparison
        π i s₀ U hU hcontains s t hs hst V hV haV N c q hq =
    (Principal.AdditiveSections.forgetScalars U).map (localPure i U hU t K c hK N e q) ≫
      SingleCoordinates.originalMap
        π i s₀ U hU hcontains s t hs hst V hV haV N c q hq := by
  rw [SingleCoordinates.comparison]
  simp only [localMap, Functor.map_comp, Category.assoc]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalPoint.PureCoordinates
