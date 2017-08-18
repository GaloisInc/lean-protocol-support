import galois.list

-- This represents a Gregorian calendar time.
structure calendar_time :=
(year   : ℕ)
(month  : fin 12)
(day    : ℕ)
(hour   : ℕ)
(minute : ℕ)
(second : ℕ)

namespace calendar_time

def month_names : list string :=
  [ "January", "February", "March", "April", "May", "June"
  , "July", "August", "September", "October", "November", "December"
  ]

def pp_2d (x : ℕ) : string :=
  if x < 10 then
    "0" ++ to_string x
  else
    to_string x

def pp_4d (x : ℕ) : string :=
  if x < 10 then
    "000" ++ to_string x
  else if x < 100 then
    "00" ++ to_string x
  else if x < 1000 then
    "0" ++ to_string x
  else
    to_string x

-- Pretty print a calendar time as an ISO8601 time
def to_iso8601 (t:calendar_time) : string :=
  let mname := month_names.fin_nth t.month in
  let dname := to_string (t.day + 1) in
  pp_4d t.year ++ "-" ++ pp_2d (t.month.val+1) ++ "-" ++ pp_2d (t.day+1)
  ++ "T" ++ pp_2d t.hour ++ ":" ++ pp_2d t.minute ++ ":" ++ pp_2d t.second
  ++ "Z"

instance : has_to_string calendar_time := ⟨to_iso8601⟩

-- Return Boolean indicating if this is a leap year.
def is_leap_year (year : ℕ) : bool :=
  year.mod 4 = 0 ∧ (year.mod 100 ≠ 0 ∨ year.mod 400 = 0)

-- Return number of days in the given year
def number_of_days (year : ℕ) : ℕ := if is_leap_year year = tt then 366 else 365

-- Number of leap years that occured since the start of 1970.
def leap_year_count (year_offset : ℕ) : ℕ :=
  -- Get number of multiples of 4 past.
  let four_mul_count         := (year_offset + (  4 -  3)).div   4 in
  -- Get number of multiples of 100 past.
  let hundred_mul_count      := (year_offset + (100 - 31)).div 100 in
  -- Get number of multiples of 400 past.
  let four_hundred_mul_count := (year_offset + (400 - 31)).div 400 in
  -- Sum up leap years
  four_mul_count - hundred_mul_count + four_hundred_mul_count

def calculate_year_and_day_offsets (days : ℕ) : ℕ × ℕ :=
  let y_off := days.div 365 in
  let total_days := 365 * y_off + leap_year_count y_off in
  let year := 1970 + y_off in
  if total_days > days then
    let adj_days := total_days - number_of_days year in
    (year - 1, days - adj_days)
  else
    (year, days - total_days)

def day_counts      : list ℕ := [31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31]
def leap_day_counts : list ℕ := [31, 29, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31]

-- This maps a posix unix time to a Gregorian calendar.
--
-- One potential issue is that if the second count corresponds to a leap second, then
-- this will create a calendar time as 23:59:59 even though that time doesn't exist.
def from_posix_unix_time (sec : ℕ) : calendar_time :=
 let min := sec.div 60 in
 let hours := min.div 60 in
 let days  := hours.div 24 in
 let (year, d_off) := calculate_year_and_day_offsets days in
 let dc := if is_leap_year year then
             leap_day_counts
           else
             day_counts in
 let ds := dc.map_accuml (λc d, ((c,c+d), c+d)) 0 in
 let pair : fin 12 × ℕ :=
       match list.first_index_of (λ(c : ℕ × ℕ), c.snd > d_off) ds.fst with
       | option.some (i,s) :=
          if p : i < 12 then
            (⟨i,p⟩,d_off - s.fst)
          else
            (0,0)
       | option.none := (0,0)
       end in
 { year := year
 , month := pair.fst
 , day := pair.snd
 , hour   := hours.mod 24
 , minute := min.mod 60
 , second := sec.mod 60
 }

end calendar_time

#eval to_string (calendar_time.from_posix_unix_time 1503071355) == "2017-08-18T15:49:15Z"
