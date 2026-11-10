import unittest
from check_source_hygiene import without_comments

class Comments(unittest.TestCase):
    def test_nested(self):
        self.assertEqual(without_comments('/- a /- b -/ c -/sorry').strip(), 'sorry')
    def test_line(self):
        self.assertEqual(without_comments('-- sorry\naxiom').splitlines()[1], 'axiom')
    def test_string(self):
        self.assertEqual(without_comments('"/-" sorry'), '"/-" sorry')
    def test_escape(self):
        s = '"a\\\"/-" sorry'
        self.assertEqual(without_comments(s), s)
    def test_lines(self):
        self.assertEqual(without_comments('/-\nsorry\n-/\nadmit').count('\n'), 3)
    def test_adjacent(self):
        self.assertEqual(without_comments('/--/sorry').strip(), 'sorry')

if __name__ == '__main__':
    unittest.main()
