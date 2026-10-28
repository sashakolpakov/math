import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalReference.CoverShiftedMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalPoint.RelativeGeometry

/-! # Shifted Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalPoint.ShiftedMap

noncomputable section

/-! For the genuine complement of a closed point, the source geometry
supplies all refinement inverses needed by the shifted pure comparison. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalPoint.RelativeGeometry
variable {X Y T S : Scheme.{u}} [X.IsSeparated] [Y.IsSeparated]
  (π : Y ⟶ S) (i : X ⟶ Y) [IsClosedImmersion i] (s₀ : T ⟶ X) [IsClosedImmersion s₀]
  (U : Y.Opens) (hU : IsAffineOpen U) (hfU : ⊤ ≤ (s₀ ≫ i) ⁻¹ᵁ U)
  {a b : ℕ} (s : Fin a → Γ(Y, U)) (t : Fin b → Γ(Y, U))
  (hs : Ideal.span (Set.range s) = i.ker.ideal ⟨U, hU⟩)
  (hst : Ideal.span (Set.range (Fin.append s t)) = (s₀ ≫ i).ker.ideal ⟨U, hU⟩)
  {κ : Type u} [LinearOrder κ] (V : κ → Y.Opens) (hV : iSup V = ⊤)
  (haV : ∀ j, IsAffineOpen (V j))
  (K : CochainComplex Y.Modules ℕ) [∀ q, (K.X q).IsQuasicoherent]
  (c : ℕ) (hK : ∀ q, q ≠ c → K.ExactAt q)
  (N : X.Modules) [N.IsQuasicoherent]
  (e : K.homology c ≅ (Scheme.Modules.pushforward i).obj N)
  (g q : ℕ) (hq : q=g+c)

abbrev comparison := by
  let D := (Scheme.Modules.pushforward i).obj N
  letI : D.IsQuasicoherent := AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom i
  letI : (K.homology c).IsQuasicoherent := QuasicoherentTruncation.cohomology K c
  letI (k : ℕ) : (((single Y.Modules (.up ℕ) c).obj (K.homology c)).X k).IsQuasicoherent :=
    QuasicoherentTruncation.single (K.homology c) c k
  letI (k : ℕ) : (((single Y.Modules (.up ℕ) c).obj D).X k).IsQuasicoherent :=
    QuasicoherentTruncation.single D c k
  letI := RelativeGeometry.right_isIso i s₀ U hU s t hs hst K c hK N e q
  letI := RelativeGeometry.right_isIso i s₀ U hU s t hs hst
    ((single Y.Modules (.up ℕ) c).obj (K.homology c)) c
    (fun k hk => exactAt_single_obj (.up ℕ) c (K.homology c) k hk) N
    (singleObjHomologySelfIso (.up ℕ) c (K.homology c) ≪≫ e) q
  letI := RelativeGeometry.right_isIso i s₀ U hU s t hs hst
    ((single Y.Modules (.up ℕ) c).obj D) c
    (fun k hk => exactAt_single_obj (.up ℕ) c D k hk) N
    (singleObjHomologySelfIso (.up ℕ) c D) q
  exact PrincipalReference.CoverShiftedMap.Reference.comparison π U hU
    (Fraction.family U t) (s₀ ≫ i) hfU
    (RelativeGeometry.common i s₀ U hU t) (RelativeGeometry.common_affine i s₀ U hU t)
    (RelativeGeometry.left i s₀ U hU t) (RelativeGeometry.right i s₀ U hU t) V hV haV K c hK D e.hom g q hq

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalPoint.ShiftedMap
