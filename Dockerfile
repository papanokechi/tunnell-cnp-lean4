FROM python:3.11-slim

WORKDIR /app
COPY requirements.txt .
RUN pip install --no-cache-dir -r requirements.txt

COPY . .

# Verify environment
RUN python -m pytest tests/test_env.py -q

# Default: run baseline counts for n <= 50
CMD ["python", "-m", "src.runner", "--max-n", "50", "--mode", "counts"]
