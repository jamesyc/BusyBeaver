module

public import Std

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-! Exact reconstructed PA215 transition table. Alphabet false/true is 0/1;
    working controls are Fin 215; none is the separate halt control.
    This module does not assert nonhalting or PA independence. -/
namespace PA215

abbrev WorkingState := Fin 215
abbrev Control := Option WorkingState

def target (n : Nat) : Control :=
  if h : n < 215 then some ⟨n, h⟩ else none

structure Action where
  write : Bool
  right : Bool
  next : Control
  deriving DecidableEq, Repr

/-- The exact 430 literal rows from dense table SHA256 89c0a100… . -/
def row (q : WorkingState) (b : Bool) : Action :=
  match q.val with
  | 0 => if b then ⟨true, true, target 64⟩ else ⟨true, true, target 1⟩
  | 1 => if b then ⟨true, true, target 1⟩ else ⟨true, true, target 91⟩
  | 2 => if b then ⟨true, false, target 3⟩ else ⟨false, false, target 2⟩
  | 3 => if b then ⟨true, false, target 3⟩ else ⟨false, false, target 4⟩
  | 4 => if b then ⟨true, false, target 3⟩ else ⟨false, false, target 6⟩
  | 5 => if b then ⟨false, false, target 5⟩ else ⟨true, true, target 7⟩
  | 6 => if b then ⟨true, false, target 3⟩ else ⟨false, false, target 10⟩
  | 7 => if b then ⟨false, true, target 11⟩ else ⟨false, true, target 7⟩
  | 8 => if b then ⟨true, true, target 186⟩ else ⟨false, true, target 83⟩
  | 9 => if b then ⟨true, true, target 14⟩ else ⟨false, true, target 15⟩
  | 10 => if b then ⟨true, false, target 3⟩ else ⟨false, false, target 16⟩
  | 11 => if b then ⟨false, true, target 11⟩ else ⟨false, false, target 17⟩
  | 12 => if b then ⟨true, true, target 19⟩ else ⟨false, false, target 27⟩
  | 13 => if b then ⟨true, true, target 21⟩ else ⟨false, true, target 20⟩
  | 14 => if b then ⟨true, false, target 32⟩ else ⟨false, false, target 88⟩
  | 15 => if b then ⟨false, true, target 23⟩ else ⟨false, false, target 12⟩
  | 16 => if b then ⟨true, false, target 3⟩ else ⟨false, false, target 24⟩
  | 17 => if b then ⟨false, false, target 2⟩ else ⟨true, false, target 2⟩
  | 18 => if b then ⟨false, true, target 33⟩ else ⟨false, true, target 25⟩
  | 19 => if b then ⟨false, false, target 104⟩ else ⟨false, true, target 93⟩
  | 20 => if b then ⟨true, true, target 30⟩ else ⟨false, true, target 29⟩
  | 21 => if b then ⟨true, true, target 32⟩ else ⟨false, true, target 31⟩
  | 22 => if b then ⟨false, true, target 60⟩ else ⟨false, true, target 25⟩
  | 23 => if b then ⟨true, true, target 23⟩ else ⟨false, true, target 34⟩
  | 24 => if b then ⟨true, false, target 3⟩ else ⟨false, false, target 35⟩
  | 25 => if b then ⟨false, true, target 1⟩ else ⟨false, false, target 36⟩
  | 26 => if b then ⟨true, true, target 26⟩ else ⟨false, true, target 37⟩
  | 27 => if b then ⟨true, true, target 38⟩ else ⟨false, true, target 177⟩
  | 28 => if b then ⟨false, false, target 40⟩ else ⟨false, true, target 39⟩
  | 29 => if b then ⟨true, true, target 42⟩ else ⟨false, true, target 41⟩
  | 30 => if b then ⟨true, true, target 44⟩ else ⟨false, true, target 43⟩
  | 31 => if b then ⟨true, true, target 46⟩ else ⟨false, true, target 45⟩
  | 32 => if b then ⟨true, true, target 47⟩ else ⟨false, true, target 22⟩
  | 33 => if b then ⟨true, true, target 33⟩ else ⟨false, true, target 48⟩
  | 34 => if b then ⟨true, true, target 34⟩ else ⟨false, true, target 33⟩
  | 35 => if b then ⟨true, false, target 3⟩ else ⟨false, false, target 50⟩
  | 36 => if b then ⟨true, false, target 2⟩ else ⟨true, true, target 36⟩
  | 37 => if b then ⟨true, true, target 37⟩ else ⟨false, true, target 51⟩
  | 38 => if b then ⟨true, true, target 53⟩ else ⟨false, true, target 14⟩
  | 39 => if b then ⟨false, true, target 37⟩ else ⟨false, false, target 12⟩
  | 40 => if b then ⟨true, false, target 54⟩ else ⟨false, false, target 5⟩
  | 41 => if b then ⟨false, true, target 26⟩ else ⟨false, true, target 25⟩
  | 42 => if b then ⟨false, false, target 17⟩ else ⟨false, true, target 14⟩
  | 43 => if b then ⟨true, true, target 57⟩ else ⟨false, true, target 56⟩
  | 44 => if b then ⟨true, true, target 59⟩ else ⟨false, true, target 58⟩
  | 45 => if b then ⟨false, true, target 55⟩ else ⟨false, true, target 25⟩
  | 46 => if b then ⟨true, true, target 62⟩ else ⟨false, true, target 61⟩
  | 47 => if b then ⟨false, false, target 17⟩ else ⟨false, true, target 63⟩
  | 48 => if b then ⟨true, true, target 48⟩ else ⟨false, true, target 26⟩
  | 49 => if b then ⟨false, true, target 64⟩ else ⟨false, false, target 36⟩
  | 50 => if b then ⟨true, false, target 3⟩ else ⟨false, false, target 74⟩
  | 51 => if b then ⟨true, true, target 51⟩ else ⟨false, true, target 17⟩
  | 52 => if b then ⟨true, true, target 141⟩ else ⟨false, true, target 145⟩
  | 53 => if b then ⟨true, true, target 69⟩ else ⟨false, true, target 68⟩
  | 54 => if b then ⟨true, false, target 54⟩ else ⟨false, false, target 40⟩
  | 55 => if b then ⟨true, true, target 55⟩ else ⟨false, true, target 23⟩
  | 56 => if b then ⟨false, true, target 51⟩ else ⟨false, false, target 12⟩
  | 57 => if b then ⟨false, false, target 17⟩ else ⟨false, true, target 61⟩
  | 58 => if b then ⟨true, true, target 71⟩ else ⟨false, true, target 70⟩
  | 59 => if b then ⟨true, true, target 72⟩ else ⟨false, true, target 62⟩
  | 60 => if b then ⟨true, true, target 60⟩ else ⟨false, true, target 55⟩
  | 61 => if b then ⟨false, true, target 26⟩ else ⟨false, true, target 49⟩
  | 62 => if b then ⟨true, false, target 73⟩ else ⟨false, false, target 29⟩
  | 63 => if b then ⟨true, false, target 31⟩ else ⟨false, false, target 116⟩
  | 64 => if b then ⟨true, true, target 64⟩ else ⟨false, true, target 0⟩
  | 65 => if b then ⟨true, true, target 147⟩ else ⟨false, true, target 96⟩
  | 66 => if b then ⟨true, false, target 54⟩ else ⟨true, true, target 180⟩
  | 67 => if b then ⟨true, true, target 143⟩ else ⟨false, true, target 142⟩
  | 68 => if b then ⟨true, true, target 215⟩ else ⟨false, true, target 76⟩
  | 69 => if b then ⟨true, true, target 32⟩ else ⟨false, false, target 192⟩
  | 70 => if b then ⟨true, true, target 63⟩ else ⟨false, true, target 41⟩
  | 71 => if b then ⟨true, true, target 77⟩ else ⟨false, false, target 88⟩
  | 72 => if b then ⟨true, false, target 78⟩ else ⟨false, true, target 56⟩
  | 73 => if b then ⟨true, true, target 80⟩ else ⟨false, true, target 79⟩
  | 74 => if b then ⟨true, true, target 81⟩ else ⟨false, true, target 74⟩
  | 75 => if b then ⟨true, false, target 139⟩ else ⟨false, false, target 143⟩
  | 76 => if b then ⟨true, true, target 85⟩ else ⟨false, true, target 84⟩
  | 77 => if b then ⟨true, false, target 131⟩ else ⟨false, true, target 88⟩
  | 78 => if b then ⟨true, true, target 57⟩ else ⟨false, false, target 107⟩
  | 79 => if b then ⟨false, true, target 34⟩ else ⟨false, true, target 49⟩
  | 80 => if b then ⟨false, false, target 42⟩ else ⟨false, true, target 90⟩
  | 81 => if b then ⟨true, true, target 211⟩ else ⟨false, true, target 173⟩
  | 82 => if b then ⟨true, true, target 13⟩ else ⟨false, true, target 95⟩
  | 83 => if b then ⟨true, true, target 96⟩ else ⟨false, true, target 87⟩
  | 84 => if b then ⟨true, true, target 22⟩ else ⟨false, true, target 202⟩
  | 85 => if b then ⟨true, true, target 99⟩ else ⟨false, true, target 115⟩
  | 86 => if b then ⟨true, true, target 112⟩ else ⟨false, true, target 147⟩
  | 87 => if b then ⟨true, true, target 102⟩ else ⟨false, true, target 101⟩
  | 88 => if b then ⟨true, true, target 78⟩ else ⟨false, true, target 79⟩
  | 89 => if b then ⟨true, true, target 170⟩ else ⟨false, true, target 100⟩
  | 90 => if b then ⟨true, true, target 105⟩ else ⟨false, true, target 104⟩
  | 91 => if b then ⟨false, true, target 1⟩ else ⟨false, true, target 66⟩
  | 92 => if b then ⟨true, true, target 106⟩ else ⟨false, true, target 28⟩
  | 93 => if b then ⟨true, true, target 97⟩ else ⟨false, true, target 98⟩
  | 94 => if b then ⟨true, false, target 94⟩ else ⟨true, false, target 109⟩
  | 95 => if b then ⟨true, true, target 110⟩ else ⟨false, true, target 20⟩
  | 96 => if b then ⟨true, true, target 61⟩ else ⟨false, true, target 61⟩
  | 97 => if b then ⟨true, true, target 153⟩ else ⟨false, true, target 163⟩
  | 98 => if b then ⟨true, true, target 111⟩ else ⟨false, false, target 27⟩
  | 99 => if b then ⟨false, false, target 203⟩ else ⟨false, true, target 104⟩
  | 100 => if b then ⟨true, true, target 117⟩ else ⟨false, true, target 116⟩
  | 101 => if b then ⟨true, true, target 59⟩ else ⟨false, true, target 72⟩
  | 102 => if b then ⟨true, true, target 118⟩ else ⟨false, true, target 58⟩
  | 103 => if b then ⟨true, true, target 119⟩ else ⟨false, true, target 22⟩
  | 104 => if b then ⟨false, false, target 11⟩ else ⟨false, true, target 22⟩
  | 105 => if b then ⟨true, true, target 42⟩ else ⟨false, true, target 62⟩
  | 106 => if b then ⟨true, true, target 9⟩ else ⟨false, true, target 120⟩
  | 107 => if b then ⟨true, true, target 121⟩ else ⟨false, true, target 100⟩
  | 108 => if b then ⟨true, true, target 169⟩ else ⟨false, true, target 87⟩
  | 109 => if b then ⟨false, false, target 94⟩ else ⟨false, false, target 203⟩
  | 110 => if b then ⟨true, true, target 103⟩ else ⟨false, true, target 123⟩
  | 111 => if b then ⟨false, false, target 203⟩ else ⟨false, true, target 114⟩
  | 112 => if b then ⟨true, true, target 177⟩ else ⟨false, true, target 108⟩
  | 113 => if b then ⟨true, true, target 144⟩ else ⟨false, true, target 146⟩
  | 114 => if b then ⟨true, true, target 122⟩ else ⟨false, true, target 82⟩
  | 115 => if b then ⟨false, false, target 2⟩ else ⟨false, false, target 130⟩
  | 116 => if b then ⟨true, true, target 73⟩ else ⟨false, true, target 39⟩
  | 117 => if b then ⟨true, true, target 131⟩ else ⟨false, true, target 62⟩
  | 118 => if b then ⟨true, true, target 132⟩ else ⟨false, true, target 62⟩
  | 119 => if b then ⟨false, false, target 17⟩ else ⟨false, true, target 71⟩
  | 120 => if b then ⟨true, true, target 131⟩ else ⟨false, true, target 15⟩
  | 121 => if b then ⟨true, true, target 133⟩ else ⟨false, true, target 22⟩
  | 122 => if b then ⟨true, true, target 128⟩ else ⟨false, true, target 127⟩
  | 123 => if b then ⟨true, false, target 21⟩ else ⟨false, true, target 135⟩
  | 124 => if b then ⟨true, true, target 176⟩ else ⟨false, true, target 129⟩
  | 125 => if b then ⟨true, true, target 167⟩ else ⟨false, true, target 200⟩
  | 126 => if b then ⟨true, true, target 172⟩ else ⟨false, true, target 75⟩
  | 127 => if b then ⟨true, true, target 134⟩ else ⟨false, true, target 83⟩
  | 128 => if b then ⟨true, true, target 136⟩ else ⟨false, true, target 125⟩
  | 129 => if b then ⟨true, true, target 139⟩ else ⟨false, true, target 13⟩
  | 130 => if b then ⟨true, true, target 70⟩ else ⟨false, true, target 31⟩
  | 131 => if b then ⟨true, false, target 123⟩ else ⟨false, true, target 39⟩
  | 132 => if b then ⟨false, false, target 17⟩ else ⟨false, true, target 150⟩
  | 133 => if b then ⟨false, false, target 17⟩ else ⟨false, true, target 151⟩
  | 134 => if b then ⟨true, true, target 148⟩ else ⟨false, true, target 137⟩
  | 135 => if b then ⟨false, true, target 48⟩ else ⟨false, true, target 25⟩
  | 136 => if b then ⟨true, true, target 152⟩ else ⟨false, true, target 146⟩
  | 137 => if b then ⟨true, true, target 156⟩ else ⟨false, true, target 157⟩
  | 138 => if b then ⟨true, true, target 155⟩ else ⟨false, true, target 95⟩
  | 139 => if b then ⟨true, true, target 162⟩ else ⟨false, true, target 171⟩
  | 140 => if b then ⟨true, true, target 155⟩ else ⟨false, true, target 13⟩
  | 141 => if b then ⟨true, false, target 162⟩ else ⟨false, true, target 87⟩
  | 142 => if b then ⟨true, true, target 154⟩ else ⟨false, true, target 87⟩
  | 143 => if b then ⟨true, false, target 159⟩ else ⟨false, false, target 149⟩
  | 144 => if b then ⟨true, true, target 87⟩ else ⟨false, true, target 83⟩
  | 145 => if b then ⟨true, true, target 13⟩ else ⟨false, true, target 155⟩
  | 146 => if b then ⟨true, true, target 141⟩ else ⟨false, true, target 82⟩
  | 147 => if b then ⟨true, false, target 139⟩ else ⟨false, false, target 67⟩
  | 148 => if b then ⟨true, true, target 165⟩ else ⟨false, true, target 188⟩
  | 149 => if b then ⟨true, true, target 113⟩ else ⟨false, true, target 155⟩
  | 150 => if b then ⟨true, true, target 96⟩ else ⟨false, true, target 96⟩
  | 151 => if b then ⟨false, true, target 33⟩ else ⟨false, true, target 49⟩
  | 152 => if b then ⟨true, true, target 182⟩ else ⟨false, true, target 174⟩
  | 153 => if b then ⟨true, true, target 95⟩ else ⟨false, false, target 206⟩
  | 154 => if b then ⟨true, true, target 175⟩ else ⟨false, true, target 164⟩
  | 155 => if b then ⟨true, true, target 166⟩ else ⟨false, true, target 20⟩
  | 156 => if b then ⟨true, true, target 142⟩ else ⟨false, true, target 183⟩
  | 157 => if b then ⟨true, true, target 95⟩ else ⟨false, true, target 155⟩
  | 158 => if b then ⟨true, true, target 160⟩ else ⟨false, true, target 124⟩
  | 159 => if b then ⟨true, true, target 158⟩ else ⟨false, true, target 96⟩
  | 160 => if b then ⟨true, true, target 140⟩ else ⟨false, false, target 8⟩
  | 161 => if b then ⟨true, true, target 169⟩ else ⟨false, true, target 147⟩
  | 162 => if b then ⟨true, true, target 168⟩ else ⟨false, true, target 144⟩
  | 163 => if b then ⟨true, true, target 29⟩ else ⟨false, true, target 192⟩
  | 164 => if b then ⟨true, true, target 141⟩ else ⟨false, true, target 157⟩
  | 165 => if b then ⟨true, true, target 144⟩ else ⟨false, true, target 67⟩
  | 166 => if b then ⟨true, true, target 121⟩ else ⟨false, true, target 177⟩
  | 167 => if b then ⟨true, true, target 161⟩ else ⟨false, true, target 143⟩
  | 168 => if b then ⟨true, true, target 61⟩ else ⟨false, true, target 75⟩
  | 169 => if b then ⟨true, true, target 87⟩ else ⟨false, true, target 143⟩
  | 170 => if b then ⟨true, true, target 95⟩ else ⟨false, true, target 103⟩
  | 171 => if b then ⟨true, true, target 83⟩ else ⟨false, true, target 138⟩
  | 172 => if b then ⟨true, true, target 75⟩ else ⟨false, true, target 171⟩
  | 173 => if b then ⟨true, true, target 107⟩ else ⟨false, true, target 92⟩
  | 174 => if b then ⟨true, true, target 184⟩ else ⟨false, true, target 149⟩
  | 175 => if b then ⟨true, true, target 52⟩ else ⟨false, true, target 96⟩
  | 176 => if b then ⟨true, true, target 52⟩ else ⟨false, true, target 164⟩
  | 177 => if b then ⟨true, false, target 130⟩ else ⟨false, true, target 18⟩
  | 178 => if b then ⟨true, true, target 115⟩ else ⟨false, true, target 76⟩
  | 179 => if b then ⟨true, true, target 123⟩ else ⟨false, true, target 105⟩
  | 180 => if b then ⟨true, false, target 109⟩ else ⟨false, false, target 40⟩
  | 181 => if b then ⟨true, true, target 155⟩ else ⟨false, true, target 167⟩
  | 182 => if b then ⟨true, true, target 190⟩ else ⟨false, true, target 185⟩
  | 183 => if b then ⟨true, true, target 194⟩ else ⟨false, true, target 191⟩
  | 184 => if b then ⟨true, true, target 196⟩ else ⟨false, true, target 195⟩
  | 185 => if b then ⟨true, true, target 198⟩ else ⟨false, true, target 197⟩
  | 186 => if b then ⟨true, true, target 187⟩ else ⟨false, true, target 153⟩
  | 187 => if b then ⟨true, true, target 181⟩ else ⟨false, true, target 171⟩
  | 188 => if b then ⟨true, true, target 8⟩ else ⟨false, true, target 65⟩
  | 189 => if b then ⟨true, true, target 126⟩ else ⟨false, true, target 147⟩
  | 190 => if b then ⟨true, true, target 199⟩ else ⟨false, true, target 86⟩
  | 191 => if b then ⟨true, true, target 201⟩ else ⟨false, true, target 69⟩
  | 192 => if b then ⟨true, true, target 87⟩ else ⟨false, true, target 89⟩
  | 193 => if b then ⟨true, true, target 213⟩ else ⟨false, true, target 29⟩
  | 194 => if b then ⟨true, true, target 204⟩ else ⟨false, true, target 138⟩
  | 195 => if b then ⟨true, true, target 205⟩ else ⟨false, true, target 145⟩
  | 196 => if b then ⟨true, true, target 207⟩ else ⟨false, true, target 52⟩
  | 197 => if b then ⟨true, true, target 208⟩ else ⟨false, true, target 155⟩
  | 198 => if b then ⟨true, true, target 210⟩ else ⟨false, true, target 209⟩
  | 199 => if b then ⟨true, true, target 212⟩ else ⟨false, true, target 178⟩
  | 200 => if b then ⟨true, true, target 189⟩ else ⟨false, true, target 159⟩
  | 201 => if b then ⟨true, true, target 192⟩ else ⟨false, true, target 87⟩
  | 202 => if b then ⟨true, true, target 99⟩ else ⟨false, true, target 45⟩
  | 203 => if b then ⟨false, false, target 203⟩ else ⟨false, false, target 5⟩
  | 204 => if b then ⟨true, true, target 214⟩ else ⟨false, true, target 160⟩
  | 205 => if b then ⟨true, true, target 155⟩ else ⟨false, true, target 146⟩
  | 206 => if b then ⟨true, true, target 178⟩ else ⟨false, true, target 207⟩
  | 207 => if b then ⟨true, true, target 52⟩ else ⟨false, true, target 141⟩
  | 208 => if b then ⟨true, true, target 108⟩ else ⟨false, true, target 108⟩
  | 209 => if b then ⟨true, true, target 155⟩ else ⟨false, true, target 83⟩
  | 210 => if b then ⟨true, true, target 108⟩ else ⟨false, true, target 52⟩
  | 211 => if b then ⟨true, true, target 193⟩ else ⟨false, true, target 12⟩
  | 212 => if b then ⟨true, true, target 178⟩ else ⟨false, true, target 179⟩
  | 213 => if b then ⟨true, true, target 38⟩ else ⟨false, true, target 21⟩
  | 214 => if b then ⟨true, true, target 87⟩ else ⟨false, true, target 87⟩
  | _ => ⟨false, false, none⟩

def start : Control := target 0
def dispatcher : Control := target 81
def halt : Control := none

def denseTarget (c : Control) : Nat := c.elim 215 Fin.val

def renderRow (q : Nat) (b : Bool) (a : Action) : String :=
  toString q ++ " " ++ (if b then "1" else "0") ++ " " ++
  (if a.write then "1" else "0") ++ " " ++ (if a.right then "R" else "L") ++
  " " ++ toString (denseTarget a.next) ++ "\n"

def workingStates : List WorkingState := List.finRange 215

def renderTable : String :=
  "#! start 0\n#! halt 215\n# Binary alphabet 0/1; blank 0; bi-infinite tape.\n" ++
  String.join (workingStates.flatMap fun q => [renderRow q.val false (row q false),
    renderRow q.val true (row q true)])

/-- Literal source-file record. `exact_source_rows` checks every semantic row;
    independent publication review also checks this record against the pinned file bytes. -/
def sourceText : String := "#! start 0\n#! halt 215\n# Binary alphabet 0/1; blank 0; bi-infinite tape.\n0 0 1 R 1\n0 1 1 R 64\n1 0 1 R 91\n1 1 1 R 1\n2 0 0 L 2\n2 1 1 L 3\n3 0 0 L 4\n3 1 1 L 3\n4 0 0 L 6\n4 1 1 L 3\n5 0 1 R 7\n5 1 0 L 5\n6 0 0 L 10\n6 1 1 L 3\n7 0 0 R 7\n7 1 0 R 11\n8 0 0 R 83\n8 1 1 R 186\n9 0 0 R 15\n9 1 1 R 14\n10 0 0 L 16\n10 1 1 L 3\n11 0 0 L 17\n11 1 0 R 11\n12 0 0 L 27\n12 1 1 R 19\n13 0 0 R 20\n13 1 1 R 21\n14 0 0 L 88\n14 1 1 L 32\n15 0 0 L 12\n15 1 0 R 23\n16 0 0 L 24\n16 1 1 L 3\n17 0 1 L 2\n17 1 0 L 2\n18 0 0 R 25\n18 1 0 R 33\n19 0 0 R 93\n19 1 0 L 104\n20 0 0 R 29\n20 1 1 R 30\n21 0 0 R 31\n21 1 1 R 32\n22 0 0 R 25\n22 1 0 R 60\n23 0 0 R 34\n23 1 1 R 23\n24 0 0 L 35\n24 1 1 L 3\n25 0 0 L 36\n25 1 0 R 1\n26 0 0 R 37\n26 1 1 R 26\n27 0 0 R 177\n27 1 1 R 38\n28 0 0 R 39\n28 1 0 L 40\n29 0 0 R 41\n29 1 1 R 42\n30 0 0 R 43\n30 1 1 R 44\n31 0 0 R 45\n31 1 1 R 46\n32 0 0 R 22\n32 1 1 R 47\n33 0 0 R 48\n33 1 1 R 33\n34 0 0 R 33\n34 1 1 R 34\n35 0 0 L 50\n35 1 1 L 3\n36 0 1 R 36\n36 1 1 L 2\n37 0 0 R 51\n37 1 1 R 37\n38 0 0 R 14\n38 1 1 R 53\n39 0 0 L 12\n39 1 0 R 37\n40 0 0 L 5\n40 1 1 L 54\n41 0 0 R 25\n41 1 0 R 26\n42 0 0 R 14\n42 1 0 L 17\n43 0 0 R 56\n43 1 1 R 57\n44 0 0 R 58\n44 1 1 R 59\n45 0 0 R 25\n45 1 0 R 55\n46 0 0 R 61\n46 1 1 R 62\n47 0 0 R 63\n47 1 0 L 17\n48 0 0 R 26\n48 1 1 R 48\n49 0 0 L 36\n49 1 0 R 64\n50 0 0 L 74\n50 1 1 L 3\n51 0 0 R 17\n51 1 1 R 51\n52 0 0 R 145\n52 1 1 R 141\n53 0 0 R 68\n53 1 1 R 69\n54 0 0 L 40\n54 1 1 L 54\n55 0 0 R 23\n55 1 1 R 55\n56 0 0 L 12\n56 1 0 R 51\n57 0 0 R 61\n57 1 0 L 17\n58 0 0 R 70\n58 1 1 R 71\n59 0 0 R 62\n59 1 1 R 72\n60 0 0 R 55\n60 1 1 R 60\n61 0 0 R 49\n61 1 0 R 26\n62 0 0 L 29\n62 1 1 L 73\n63 0 0 L 116\n63 1 1 L 31\n64 0 0 R 0\n64 1 1 R 64\n65 0 0 R 96\n65 1 1 R 147\n66 0 1 R 180\n66 1 1 L 54\n67 0 0 R 142\n67 1 1 R 143\n68 0 0 R 76\n68 1 1 R 215\n69 0 0 L 192\n69 1 1 R 32\n70 0 0 R 41\n70 1 1 R 63\n71 0 0 L 88\n71 1 1 R 77\n72 0 0 R 56\n72 1 1 L 78\n73 0 0 R 79\n73 1 1 R 80\n74 0 0 R 74\n74 1 1 R 81\n75 0 0 L 143\n75 1 1 L 139\n76 0 0 R 84\n76 1 1 R 85\n77 0 0 R 88\n77 1 1 L 131\n78 0 0 L 107\n78 1 1 R 57\n79 0 0 R 49\n79 1 0 R 34\n80 0 0 R 90\n80 1 0 L 42\n81 0 0 R 173\n81 1 1 R 211\n82 0 0 R 95\n82 1 1 R 13\n83 0 0 R 87\n83 1 1 R 96\n84 0 0 R 202\n84 1 1 R 22\n85 0 0 R 115\n85 1 1 R 99\n86 0 0 R 147\n86 1 1 R 112\n87 0 0 R 101\n87 1 1 R 102\n88 0 0 R 79\n88 1 1 R 78\n89 0 0 R 100\n89 1 1 R 170\n90 0 0 R 104\n90 1 1 R 105\n91 0 0 R 66\n91 1 0 R 1\n92 0 0 R 28\n92 1 1 R 106\n93 0 0 R 98\n93 1 1 R 97\n94 0 1 L 109\n94 1 1 L 94\n95 0 0 R 20\n95 1 1 R 110\n96 0 0 R 61\n96 1 1 R 61\n97 0 0 R 163\n97 1 1 R 153\n98 0 0 L 27\n98 1 1 R 111\n99 0 0 R 104\n99 1 0 L 203\n100 0 0 R 116\n100 1 1 R 117\n101 0 0 R 72\n101 1 1 R 59\n102 0 0 R 58\n102 1 1 R 118\n103 0 0 R 22\n103 1 1 R 119\n104 0 0 R 22\n104 1 0 L 11\n105 0 0 R 62\n105 1 1 R 42\n106 0 0 R 120\n106 1 1 R 9\n107 0 0 R 100\n107 1 1 R 121\n108 0 0 R 87\n108 1 1 R 169\n109 0 0 L 203\n109 1 0 L 94\n110 0 0 R 123\n110 1 1 R 103\n111 0 0 R 114\n111 1 0 L 203\n112 0 0 R 108\n112 1 1 R 177\n113 0 0 R 146\n113 1 1 R 144\n114 0 0 R 82\n114 1 1 R 122\n115 0 0 L 130\n115 1 0 L 2\n116 0 0 R 39\n116 1 1 R 73\n117 0 0 R 62\n117 1 1 R 131\n118 0 0 R 62\n118 1 1 R 132\n119 0 0 R 71\n119 1 0 L 17\n120 0 0 R 15\n120 1 1 R 131\n121 0 0 R 22\n121 1 1 R 133\n122 0 0 R 127\n122 1 1 R 128\n123 0 0 R 135\n123 1 1 L 21\n124 0 0 R 129\n124 1 1 R 176\n125 0 0 R 200\n125 1 1 R 167\n126 0 0 R 75\n126 1 1 R 172\n127 0 0 R 83\n127 1 1 R 134\n128 0 0 R 125\n128 1 1 R 136\n129 0 0 R 13\n129 1 1 R 139\n130 0 0 R 31\n130 1 1 R 70\n131 0 0 R 39\n131 1 1 L 123\n132 0 0 R 150\n132 1 0 L 17\n133 0 0 R 151\n133 1 0 L 17\n134 0 0 R 137\n134 1 1 R 148\n135 0 0 R 25\n135 1 0 R 48\n136 0 0 R 146\n136 1 1 R 152\n137 0 0 R 157\n137 1 1 R 156\n138 0 0 R 95\n138 1 1 R 155\n139 0 0 R 171\n139 1 1 R 162\n140 0 0 R 13\n140 1 1 R 155\n141 0 0 R 87\n141 1 1 L 162\n142 0 0 R 87\n142 1 1 R 154\n143 0 0 L 149\n143 1 1 L 159\n144 0 0 R 83\n144 1 1 R 87\n145 0 0 R 155\n145 1 1 R 13\n146 0 0 R 82\n146 1 1 R 141\n147 0 0 L 67\n147 1 1 L 139\n148 0 0 R 188\n148 1 1 R 165\n149 0 0 R 155\n149 1 1 R 113\n150 0 0 R 96\n150 1 1 R 96\n151 0 0 R 49\n151 1 0 R 33\n152 0 0 R 174\n152 1 1 R 182\n153 0 0 L 206\n153 1 1 R 95\n154 0 0 R 164\n154 1 1 R 175\n155 0 0 R 20\n155 1 1 R 166\n156 0 0 R 183\n156 1 1 R 142\n157 0 0 R 155\n157 1 1 R 95\n158 0 0 R 124\n158 1 1 R 160\n159 0 0 R 96\n159 1 1 R 158\n160 0 0 L 8\n160 1 1 R 140\n161 0 0 R 147\n161 1 1 R 169\n162 0 0 R 144\n162 1 1 R 168\n163 0 0 R 192\n163 1 1 R 29\n164 0 0 R 157\n164 1 1 R 141\n165 0 0 R 67\n165 1 1 R 144\n166 0 0 R 177\n166 1 1 R 121\n167 0 0 R 143\n167 1 1 R 161\n168 0 0 R 75\n168 1 1 R 61\n169 0 0 R 143\n169 1 1 R 87\n170 0 0 R 103\n170 1 1 R 95\n171 0 0 R 138\n171 1 1 R 83\n172 0 0 R 171\n172 1 1 R 75\n173 0 0 R 92\n173 1 1 R 107\n174 0 0 R 149\n174 1 1 R 184\n175 0 0 R 96\n175 1 1 R 52\n176 0 0 R 164\n176 1 1 R 52\n177 0 0 R 18\n177 1 1 L 130\n178 0 0 R 76\n178 1 1 R 115\n179 0 0 R 105\n179 1 1 R 123\n180 0 0 L 40\n180 1 1 L 109\n181 0 0 R 167\n181 1 1 R 155\n182 0 0 R 185\n182 1 1 R 190\n183 0 0 R 191\n183 1 1 R 194\n184 0 0 R 195\n184 1 1 R 196\n185 0 0 R 197\n185 1 1 R 198\n186 0 0 R 153\n186 1 1 R 187\n187 0 0 R 171\n187 1 1 R 181\n188 0 0 R 65\n188 1 1 R 8\n189 0 0 R 147\n189 1 1 R 126\n190 0 0 R 86\n190 1 1 R 199\n191 0 0 R 69\n191 1 1 R 201\n192 0 0 R 89\n192 1 1 R 87\n193 0 0 R 29\n193 1 1 R 213\n194 0 0 R 138\n194 1 1 R 204\n195 0 0 R 145\n195 1 1 R 205\n196 0 0 R 52\n196 1 1 R 207\n197 0 0 R 155\n197 1 1 R 208\n198 0 0 R 209\n198 1 1 R 210\n199 0 0 R 178\n199 1 1 R 212\n200 0 0 R 159\n200 1 1 R 189\n201 0 0 R 87\n201 1 1 R 192\n202 0 0 R 45\n202 1 1 R 99\n203 0 0 L 5\n203 1 0 L 203\n204 0 0 R 160\n204 1 1 R 214\n205 0 0 R 146\n205 1 1 R 155\n206 0 0 R 207\n206 1 1 R 178\n207 0 0 R 141\n207 1 1 R 52\n208 0 0 R 108\n208 1 1 R 108\n209 0 0 R 83\n209 1 1 R 155\n210 0 0 R 52\n210 1 1 R 108\n211 0 0 R 12\n211 1 1 R 193\n212 0 0 R 179\n212 1 1 R 178\n213 0 0 R 21\n213 1 1 R 38\n214 0 0 R 87\n214 1 1 R 87\n"


theorem working_state_count : workingStates.length = 215 := by decide

theorem binary_row_count : (workingStates.flatMap fun q => [(q, false), (q, true)]).length = 430 := by decide

theorem start_is_zero : start = some ⟨0, by decide⟩ := rfl
theorem dispatcher_is_81 : dispatcher = some ⟨81, by decide⟩ := rfl
theorem halt_is_separate : ∀ q : WorkingState, some q ≠ halt := by intro q h; cases h

/-- Independent literal row data corresponding to the published text table. -/
def sourceRows : List (Nat × Bool × Bool × Bool × Nat) := [
  (0, false, true, true, 1),
  (0, true, true, true, 64),
  (1, false, true, true, 91),
  (1, true, true, true, 1),
  (2, false, false, false, 2),
  (2, true, true, false, 3),
  (3, false, false, false, 4),
  (3, true, true, false, 3),
  (4, false, false, false, 6),
  (4, true, true, false, 3),
  (5, false, true, true, 7),
  (5, true, false, false, 5),
  (6, false, false, false, 10),
  (6, true, true, false, 3),
  (7, false, false, true, 7),
  (7, true, false, true, 11),
  (8, false, false, true, 83),
  (8, true, true, true, 186),
  (9, false, false, true, 15),
  (9, true, true, true, 14),
  (10, false, false, false, 16),
  (10, true, true, false, 3),
  (11, false, false, false, 17),
  (11, true, false, true, 11),
  (12, false, false, false, 27),
  (12, true, true, true, 19),
  (13, false, false, true, 20),
  (13, true, true, true, 21),
  (14, false, false, false, 88),
  (14, true, true, false, 32),
  (15, false, false, false, 12),
  (15, true, false, true, 23),
  (16, false, false, false, 24),
  (16, true, true, false, 3),
  (17, false, true, false, 2),
  (17, true, false, false, 2),
  (18, false, false, true, 25),
  (18, true, false, true, 33),
  (19, false, false, true, 93),
  (19, true, false, false, 104),
  (20, false, false, true, 29),
  (20, true, true, true, 30),
  (21, false, false, true, 31),
  (21, true, true, true, 32),
  (22, false, false, true, 25),
  (22, true, false, true, 60),
  (23, false, false, true, 34),
  (23, true, true, true, 23),
  (24, false, false, false, 35),
  (24, true, true, false, 3),
  (25, false, false, false, 36),
  (25, true, false, true, 1),
  (26, false, false, true, 37),
  (26, true, true, true, 26),
  (27, false, false, true, 177),
  (27, true, true, true, 38),
  (28, false, false, true, 39),
  (28, true, false, false, 40),
  (29, false, false, true, 41),
  (29, true, true, true, 42),
  (30, false, false, true, 43),
  (30, true, true, true, 44),
  (31, false, false, true, 45),
  (31, true, true, true, 46),
  (32, false, false, true, 22),
  (32, true, true, true, 47),
  (33, false, false, true, 48),
  (33, true, true, true, 33),
  (34, false, false, true, 33),
  (34, true, true, true, 34),
  (35, false, false, false, 50),
  (35, true, true, false, 3),
  (36, false, true, true, 36),
  (36, true, true, false, 2),
  (37, false, false, true, 51),
  (37, true, true, true, 37),
  (38, false, false, true, 14),
  (38, true, true, true, 53),
  (39, false, false, false, 12),
  (39, true, false, true, 37),
  (40, false, false, false, 5),
  (40, true, true, false, 54),
  (41, false, false, true, 25),
  (41, true, false, true, 26),
  (42, false, false, true, 14),
  (42, true, false, false, 17),
  (43, false, false, true, 56),
  (43, true, true, true, 57),
  (44, false, false, true, 58),
  (44, true, true, true, 59),
  (45, false, false, true, 25),
  (45, true, false, true, 55),
  (46, false, false, true, 61),
  (46, true, true, true, 62),
  (47, false, false, true, 63),
  (47, true, false, false, 17),
  (48, false, false, true, 26),
  (48, true, true, true, 48),
  (49, false, false, false, 36),
  (49, true, false, true, 64),
  (50, false, false, false, 74),
  (50, true, true, false, 3),
  (51, false, false, true, 17),
  (51, true, true, true, 51),
  (52, false, false, true, 145),
  (52, true, true, true, 141),
  (53, false, false, true, 68),
  (53, true, true, true, 69),
  (54, false, false, false, 40),
  (54, true, true, false, 54),
  (55, false, false, true, 23),
  (55, true, true, true, 55),
  (56, false, false, false, 12),
  (56, true, false, true, 51),
  (57, false, false, true, 61),
  (57, true, false, false, 17),
  (58, false, false, true, 70),
  (58, true, true, true, 71),
  (59, false, false, true, 62),
  (59, true, true, true, 72),
  (60, false, false, true, 55),
  (60, true, true, true, 60),
  (61, false, false, true, 49),
  (61, true, false, true, 26),
  (62, false, false, false, 29),
  (62, true, true, false, 73),
  (63, false, false, false, 116),
  (63, true, true, false, 31),
  (64, false, false, true, 0),
  (64, true, true, true, 64),
  (65, false, false, true, 96),
  (65, true, true, true, 147),
  (66, false, true, true, 180),
  (66, true, true, false, 54),
  (67, false, false, true, 142),
  (67, true, true, true, 143),
  (68, false, false, true, 76),
  (68, true, true, true, 215),
  (69, false, false, false, 192),
  (69, true, true, true, 32),
  (70, false, false, true, 41),
  (70, true, true, true, 63),
  (71, false, false, false, 88),
  (71, true, true, true, 77),
  (72, false, false, true, 56),
  (72, true, true, false, 78),
  (73, false, false, true, 79),
  (73, true, true, true, 80),
  (74, false, false, true, 74),
  (74, true, true, true, 81),
  (75, false, false, false, 143),
  (75, true, true, false, 139),
  (76, false, false, true, 84),
  (76, true, true, true, 85),
  (77, false, false, true, 88),
  (77, true, true, false, 131),
  (78, false, false, false, 107),
  (78, true, true, true, 57),
  (79, false, false, true, 49),
  (79, true, false, true, 34),
  (80, false, false, true, 90),
  (80, true, false, false, 42),
  (81, false, false, true, 173),
  (81, true, true, true, 211),
  (82, false, false, true, 95),
  (82, true, true, true, 13),
  (83, false, false, true, 87),
  (83, true, true, true, 96),
  (84, false, false, true, 202),
  (84, true, true, true, 22),
  (85, false, false, true, 115),
  (85, true, true, true, 99),
  (86, false, false, true, 147),
  (86, true, true, true, 112),
  (87, false, false, true, 101),
  (87, true, true, true, 102),
  (88, false, false, true, 79),
  (88, true, true, true, 78),
  (89, false, false, true, 100),
  (89, true, true, true, 170),
  (90, false, false, true, 104),
  (90, true, true, true, 105),
  (91, false, false, true, 66),
  (91, true, false, true, 1),
  (92, false, false, true, 28),
  (92, true, true, true, 106),
  (93, false, false, true, 98),
  (93, true, true, true, 97),
  (94, false, true, false, 109),
  (94, true, true, false, 94),
  (95, false, false, true, 20),
  (95, true, true, true, 110),
  (96, false, false, true, 61),
  (96, true, true, true, 61),
  (97, false, false, true, 163),
  (97, true, true, true, 153),
  (98, false, false, false, 27),
  (98, true, true, true, 111),
  (99, false, false, true, 104),
  (99, true, false, false, 203),
  (100, false, false, true, 116),
  (100, true, true, true, 117),
  (101, false, false, true, 72),
  (101, true, true, true, 59),
  (102, false, false, true, 58),
  (102, true, true, true, 118),
  (103, false, false, true, 22),
  (103, true, true, true, 119),
  (104, false, false, true, 22),
  (104, true, false, false, 11),
  (105, false, false, true, 62),
  (105, true, true, true, 42),
  (106, false, false, true, 120),
  (106, true, true, true, 9),
  (107, false, false, true, 100),
  (107, true, true, true, 121),
  (108, false, false, true, 87),
  (108, true, true, true, 169),
  (109, false, false, false, 203),
  (109, true, false, false, 94),
  (110, false, false, true, 123),
  (110, true, true, true, 103),
  (111, false, false, true, 114),
  (111, true, false, false, 203),
  (112, false, false, true, 108),
  (112, true, true, true, 177),
  (113, false, false, true, 146),
  (113, true, true, true, 144),
  (114, false, false, true, 82),
  (114, true, true, true, 122),
  (115, false, false, false, 130),
  (115, true, false, false, 2),
  (116, false, false, true, 39),
  (116, true, true, true, 73),
  (117, false, false, true, 62),
  (117, true, true, true, 131),
  (118, false, false, true, 62),
  (118, true, true, true, 132),
  (119, false, false, true, 71),
  (119, true, false, false, 17),
  (120, false, false, true, 15),
  (120, true, true, true, 131),
  (121, false, false, true, 22),
  (121, true, true, true, 133),
  (122, false, false, true, 127),
  (122, true, true, true, 128),
  (123, false, false, true, 135),
  (123, true, true, false, 21),
  (124, false, false, true, 129),
  (124, true, true, true, 176),
  (125, false, false, true, 200),
  (125, true, true, true, 167),
  (126, false, false, true, 75),
  (126, true, true, true, 172),
  (127, false, false, true, 83),
  (127, true, true, true, 134),
  (128, false, false, true, 125),
  (128, true, true, true, 136),
  (129, false, false, true, 13),
  (129, true, true, true, 139),
  (130, false, false, true, 31),
  (130, true, true, true, 70),
  (131, false, false, true, 39),
  (131, true, true, false, 123),
  (132, false, false, true, 150),
  (132, true, false, false, 17),
  (133, false, false, true, 151),
  (133, true, false, false, 17),
  (134, false, false, true, 137),
  (134, true, true, true, 148),
  (135, false, false, true, 25),
  (135, true, false, true, 48),
  (136, false, false, true, 146),
  (136, true, true, true, 152),
  (137, false, false, true, 157),
  (137, true, true, true, 156),
  (138, false, false, true, 95),
  (138, true, true, true, 155),
  (139, false, false, true, 171),
  (139, true, true, true, 162),
  (140, false, false, true, 13),
  (140, true, true, true, 155),
  (141, false, false, true, 87),
  (141, true, true, false, 162),
  (142, false, false, true, 87),
  (142, true, true, true, 154),
  (143, false, false, false, 149),
  (143, true, true, false, 159),
  (144, false, false, true, 83),
  (144, true, true, true, 87),
  (145, false, false, true, 155),
  (145, true, true, true, 13),
  (146, false, false, true, 82),
  (146, true, true, true, 141),
  (147, false, false, false, 67),
  (147, true, true, false, 139),
  (148, false, false, true, 188),
  (148, true, true, true, 165),
  (149, false, false, true, 155),
  (149, true, true, true, 113),
  (150, false, false, true, 96),
  (150, true, true, true, 96),
  (151, false, false, true, 49),
  (151, true, false, true, 33),
  (152, false, false, true, 174),
  (152, true, true, true, 182),
  (153, false, false, false, 206),
  (153, true, true, true, 95),
  (154, false, false, true, 164),
  (154, true, true, true, 175),
  (155, false, false, true, 20),
  (155, true, true, true, 166),
  (156, false, false, true, 183),
  (156, true, true, true, 142),
  (157, false, false, true, 155),
  (157, true, true, true, 95),
  (158, false, false, true, 124),
  (158, true, true, true, 160),
  (159, false, false, true, 96),
  (159, true, true, true, 158),
  (160, false, false, false, 8),
  (160, true, true, true, 140),
  (161, false, false, true, 147),
  (161, true, true, true, 169),
  (162, false, false, true, 144),
  (162, true, true, true, 168),
  (163, false, false, true, 192),
  (163, true, true, true, 29),
  (164, false, false, true, 157),
  (164, true, true, true, 141),
  (165, false, false, true, 67),
  (165, true, true, true, 144),
  (166, false, false, true, 177),
  (166, true, true, true, 121),
  (167, false, false, true, 143),
  (167, true, true, true, 161),
  (168, false, false, true, 75),
  (168, true, true, true, 61),
  (169, false, false, true, 143),
  (169, true, true, true, 87),
  (170, false, false, true, 103),
  (170, true, true, true, 95),
  (171, false, false, true, 138),
  (171, true, true, true, 83),
  (172, false, false, true, 171),
  (172, true, true, true, 75),
  (173, false, false, true, 92),
  (173, true, true, true, 107),
  (174, false, false, true, 149),
  (174, true, true, true, 184),
  (175, false, false, true, 96),
  (175, true, true, true, 52),
  (176, false, false, true, 164),
  (176, true, true, true, 52),
  (177, false, false, true, 18),
  (177, true, true, false, 130),
  (178, false, false, true, 76),
  (178, true, true, true, 115),
  (179, false, false, true, 105),
  (179, true, true, true, 123),
  (180, false, false, false, 40),
  (180, true, true, false, 109),
  (181, false, false, true, 167),
  (181, true, true, true, 155),
  (182, false, false, true, 185),
  (182, true, true, true, 190),
  (183, false, false, true, 191),
  (183, true, true, true, 194),
  (184, false, false, true, 195),
  (184, true, true, true, 196),
  (185, false, false, true, 197),
  (185, true, true, true, 198),
  (186, false, false, true, 153),
  (186, true, true, true, 187),
  (187, false, false, true, 171),
  (187, true, true, true, 181),
  (188, false, false, true, 65),
  (188, true, true, true, 8),
  (189, false, false, true, 147),
  (189, true, true, true, 126),
  (190, false, false, true, 86),
  (190, true, true, true, 199),
  (191, false, false, true, 69),
  (191, true, true, true, 201),
  (192, false, false, true, 89),
  (192, true, true, true, 87),
  (193, false, false, true, 29),
  (193, true, true, true, 213),
  (194, false, false, true, 138),
  (194, true, true, true, 204),
  (195, false, false, true, 145),
  (195, true, true, true, 205),
  (196, false, false, true, 52),
  (196, true, true, true, 207),
  (197, false, false, true, 155),
  (197, true, true, true, 208),
  (198, false, false, true, 209),
  (198, true, true, true, 210),
  (199, false, false, true, 178),
  (199, true, true, true, 212),
  (200, false, false, true, 159),
  (200, true, true, true, 189),
  (201, false, false, true, 87),
  (201, true, true, true, 192),
  (202, false, false, true, 45),
  (202, true, true, true, 99),
  (203, false, false, false, 5),
  (203, true, false, false, 203),
  (204, false, false, true, 160),
  (204, true, true, true, 214),
  (205, false, false, true, 146),
  (205, true, true, true, 155),
  (206, false, false, true, 207),
  (206, true, true, true, 178),
  (207, false, false, true, 141),
  (207, true, true, true, 52),
  (208, false, false, true, 108),
  (208, true, true, true, 108),
  (209, false, false, true, 83),
  (209, true, true, true, 155),
  (210, false, false, true, 52),
  (210, true, true, true, 108),
  (211, false, false, true, 12),
  (211, true, true, true, 193),
  (212, false, false, true, 179),
  (212, true, true, true, 178),
  (213, false, false, true, 21),
  (213, true, true, true, 38),
  (214, false, false, true, 87),
  (214, true, true, true, 87)]

def semanticRows : List (Nat × Bool × Bool × Bool × Nat) :=
  workingStates.flatMap fun q => [false, true].map fun b =>
    let a := row q b
    (q.val, b, a.write, a.right, denseTarget a.next)

/-- Kernel-checked agreement of every row's state, read, write, direction and target. -/
theorem exact_source_rows : semanticRows = sourceRows := by decide

end PA215
