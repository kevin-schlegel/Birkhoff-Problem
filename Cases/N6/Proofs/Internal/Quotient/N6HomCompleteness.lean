import N6Images0
import N6Images1
import N6Images2
import N6Images3
import N6Images4
import N6Images5
import N6Images6
import N6Images7
import N6Images8
import N6Images9
import N6Images10
import N6Images11
import N6Images12
import N6Images13
import N6Images14
import N6Images15
import N6Images16
import N6Images17
import N6Images18
import N6Images19
import N6Images20
import N6Images21
import N6Images22
import N6Images23
import N6Images24
import N6Images25
import N6Images26
import N6Images27
import N6Images28
import N6Images29
import N6Images30
import N6Images31
import N6Images32
import N6Images33
import N6Images34
import N6Images35
import N6Images36
import N6Images37
import N6Images38
import N6Images39
import N6Images40
import N6Images41
import N6Images42
import N6Images43
import N6Images44
import N6Images45
import N6Images46
noncomputable section
namespace UniserialComputations.N6
set_option maxRecDepth 10000
variable {R k : Type*} [CommRing R] [Field k] (π : R) (ρ : R →+* k)
theorem image_normal (h6 : π^6=0) (ann : ∀ r,π^5*r=0 ↔ ρ r=0) (i j : Fin 47) (f : HomData π i j) : Normal k (homKind i j) (reduceHom π ρ f) := by
  fin_cases i
  · exact image_row0 π ρ h6 ann j f
  · exact image_row1 π ρ h6 ann j f
  · exact image_row2 π ρ h6 ann j f
  · exact image_row3 π ρ h6 ann j f
  · exact image_row4 π ρ h6 ann j f
  · exact image_row5 π ρ h6 ann j f
  · exact image_row6 π ρ h6 ann j f
  · exact image_row7 π ρ h6 ann j f
  · exact image_row8 π ρ h6 ann j f
  · exact image_row9 π ρ h6 ann j f
  · exact image_row10 π ρ h6 ann j f
  · exact image_row11 π ρ h6 ann j f
  · exact image_row12 π ρ h6 ann j f
  · exact image_row13 π ρ h6 ann j f
  · exact image_row14 π ρ h6 ann j f
  · exact image_row15 π ρ h6 ann j f
  · exact image_row16 π ρ h6 ann j f
  · exact image_row17 π ρ h6 ann j f
  · exact image_row18 π ρ h6 ann j f
  · exact image_row19 π ρ h6 ann j f
  · exact image_row20 π ρ h6 ann j f
  · exact image_row21 π ρ h6 ann j f
  · exact image_row22 π ρ h6 ann j f
  · exact image_row23 π ρ h6 ann j f
  · exact image_row24 π ρ h6 ann j f
  · exact image_row25 π ρ h6 ann j f
  · exact image_row26 π ρ h6 ann j f
  · exact image_row27 π ρ h6 ann j f
  · exact image_row28 π ρ h6 ann j f
  · exact image_row29 π ρ h6 ann j f
  · exact image_row30 π ρ h6 ann j f
  · exact image_row31 π ρ h6 ann j f
  · exact image_row32 π ρ h6 ann j f
  · exact image_row33 π ρ h6 ann j f
  · exact image_row34 π ρ h6 ann j f
  · exact image_row35 π ρ h6 ann j f
  · exact image_row36 π ρ h6 ann j f
  · exact image_row37 π ρ h6 ann j f
  · exact image_row38 π ρ h6 ann j f
  · exact image_row39 π ρ h6 ann j f
  · exact image_row40 π ρ h6 ann j f
  · exact image_row41 π ρ h6 ann j f
  · exact image_row42 π ρ h6 ann j f
  · exact image_row43 π ρ h6 ann j f
  · exact image_row44 π ρ h6 ann j f
  · exact image_row45 π ρ h6 ann j f
  · exact image_row46 π ρ h6 ann j f
end UniserialComputations.N6
