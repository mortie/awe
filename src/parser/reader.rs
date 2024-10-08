#[derive(Copy, Clone)]
pub struct SeekPoint {
    idx: usize,
    line: u32,
    col: u32,
}

pub struct Reader<'a> {
    pub line: u32,
    pub col: u32,
    string: &'a [u8],
    idx: usize,
}

impl<'a> Reader<'a> {
    pub fn new(string: &'a [u8]) -> Self {
        Self {
            line: 1,
            col: 1,
            string,
            idx: 0,
        }
    }

    pub fn peek(&self) -> Option<u8> {
        self.peek_n(0)
    }

    pub fn peek_n(&self, n: usize) -> Option<u8> {
        if self.idx + n < self.string.len() {
            Some(self.string[self.idx + n])
        } else {
            None
        }
    }

    pub fn peek_cmp(&self, str: &[u8]) -> bool {
        for (i, expected) in str.iter().enumerate() {
            let Some(ch) = self.peek_n(i) else {
                return false;
            };

            if ch != *expected {
                return false;
            }
        }

        true
    }

    pub fn peek_cmp_consume(&mut self, str: &[u8]) -> bool {
        if self.peek_cmp(str) {
            self.consume_n(str.len());
            return true;
        }

        false
    }

    pub fn eof(&self) -> bool {
        self.idx == self.string.len()
    }

    pub fn consume(&mut self) {
        if self.idx < self.string.len() {
            let ch = self.string[self.idx];
            if ch == b'\n' {
                self.line += 1;
                self.col = 1;
            } else {
                self.col += 1;
            }

            self.idx += 1;
        }
    }

    pub fn consume_n(&mut self, mut n: usize) {
        while n > 0 {
            self.consume();
            n -= 1;
        }
    }

    pub fn tell(&self) -> SeekPoint {
        SeekPoint {
            idx: self.idx,
            line: self.line,
            col: self.col,
        }
    }

    pub fn seek(&mut self, point: SeekPoint) {
        self.idx = point.idx;
        self.line = point.line;
        self.col = point.col;
    }
}
