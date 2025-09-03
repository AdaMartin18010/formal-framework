from fastapi import FastAPI
from pydantic import BaseModel

app = FastAPI()

class InferenceInput(BaseModel):
    text: str

@app.post('/infer')
def infer(inp: InferenceInput):
    score = len(inp.text) % 10 / 10.0  # placeholder score
    return {"label": "ok", "score": score}
